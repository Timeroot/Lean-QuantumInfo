/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann

import QuantumInfo.ForMathlib.HermitianMat.Unitary

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.
-/

--Note: without the assumption `h`, we could still get nonnegativity, just not strict positivity.
private theorem sandwiched_trace_pos (h : σ.M.ker ≤ ρ.M.ker) :
    0 < ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  apply HermitianMat.trace_pos
  apply HermitianMat.rpow_pos
  apply HermitianMat.conj_pos ρ.pos
  grw [← h]
  exact HermitianMat.ker_rpow_le_of_nonneg σ.nonneg

/--
The Schatten p-norm of a matrix A is (Tr[(A*A)^(p/2)])^(1/p).
-/
noncomputable def schattenNorm {d : Type*} [Fintype d] [DecidableEq d] (A : Matrix d d ℂ) (p : ℝ) : ℝ :=
  RCLike.re (Matrix.IsHermitian.cfc (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose) (fun x => x ^ (p/2))).trace ^ (1/p)

/-
For a positive Hermitian matrix A, (A^2)^(p/2) = A^p, expressed using functional calculus.
-/
theorem HermitianMat.cfc_sq_rpow_eq_cfc_rpow
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (p : ℝ) (hp : 0 < p) :
    (A ^ 2).cfc (fun x => x ^ (p/2)) = A.cfc (fun x => x ^ p) := by
  have h_sqrt : (A ^ 2).cfc (fun x => x ^ (p / 2)) = (A.cfc (fun x => x ^ 2)).cfc (fun x => x ^ (p / 2)) := by
    convert rfl;
    exact cfc_pow A;
  rw [ h_sqrt ];
  have h_sqrt : ∀ (f g : ℝ → ℝ), Continuous f → Continuous g → ∀ (A : HermitianMat d ℂ), (A.cfc f).cfc g = A.cfc (fun x => g (f x)) := by
    exact fun f g a a A => Eq.symm (cfc_comp_apply A f g);
  rw [ h_sqrt ];
  · have h_sqrt : ∀ x : ℝ, 0 ≤ x → (x ^ 2) ^ (p / 2) = x ^ p := by
      intro x hx
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx ]
      ring_nf
    exact cfc_congr_of_nonneg hA h_sqrt;
  · continuity;
  · exact continuous_id.rpow_const fun x => Or.inr <| by positivity

/--
For a positive Hermitian matrix A, ||A||_p = (Tr(A^p))^(1/p).
-/
theorem schattenNorm_hermitian_pow {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) :
    schattenNorm A.mat p = (A ^ p).trace ^ (1/p) := by
  convert congr_arg ( fun x : ℝ => x ^ ( 1 / p ) ) _ using 1;
  convert congr_arg _ ( HermitianMat.cfc_sq_rpow_eq_cfc_rpow A hA p hp ) using 1;
  unfold HermitianMat.trace;
  convert rfl;
  convert HermitianMat.mat_cfc ( A ^ 2 ) ( fun x => x ^ ( p / 2 ) );
  sorry

lemma schattenNorm_pow_eq
  (A : HermitianMat d ℂ) (hA : 0 ≤ A) (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    schattenNorm (A ^ k).mat p = (schattenNorm A.mat (k * p)) ^ k := by
  rw [ schattenNorm_hermitian_pow, schattenNorm_hermitian_pow ] <;> try positivity;
  · rw [ ← Real.rpow_mul ] <;> ring_nf <;> norm_num [ hp.ne', hk.ne' ];
    · rw [ mul_comm, ← HermitianMat.rpow_mul ];
      exact hA;
    · -- Since $A$ is positive, $A^{k*p}$ is also positive, and the trace of a positive matrix is non-negative.
      have h_pos : 0 ≤ A ^ (k * p) := by
        exact HermitianMat.rpow_nonneg hA;
      exact HermitianMat.trace_nonneg h_pos;
  · exact HermitianMat.rpow_nonneg hA

lemma trace_eq_schattenNorm_rpow
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (r : ℝ) (hr : 0 < r) :
    (A ^ r).trace = (schattenNorm A.mat r) ^ r := by
  rw [schattenNorm_hermitian_pow hA hr, ← Real.rpow_mul] <;> norm_num [hr.ne']
  apply HermitianMat.trace_nonneg
  exact HermitianMat.rpow_nonneg hA

def singularValues (A : Matrix d d ℂ) : d → ℝ :=
  fun i => Real.sqrt ((Matrix.isHermitian_mul_conjTranspose_self A).eigenvalues i)

lemma singularValues_nonneg (A : Matrix d d ℂ) (i : d) :
    0 ≤ singularValues A i := by
  apply Real.sqrt_nonneg

/--
Hermitian trace Hölder inequality: for PSD A, B and conjugate exponents p, q > 1,
⟪A, B⟫ ≤ Tr[A^p]^(1/p) * Tr[B^q]^(1/q).
This follows from the von Neumann trace inequality combined with the scalar Hölder inequality.
-/
lemma HermitianMat.inner_le_trace_rpow_mul
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace ^ (1/p) * (B ^ q).trace ^ (1/q) := by
  sorry

/--
Trace subadditivity (Rotfel'd inequality): for PSD A, B and 0 < p ≤ 1,
Tr[(A + B)^p] ≤ Tr[A^p] + Tr[B^p].
This is a consequence of the concavity of x^p for 0 < p ≤ 1.
-/
lemma HermitianMat.trace_rpow_add_le
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((A + B) ^ p).trace ≤ (A ^ p).trace + (B ^ p).trace := by
  sorry

/-
PROBLEM
For a density matrix σ and r > 0, show σ.M ^ r ≤ 1.

PROVIDED SOLUTION
Since σ is PSD with eigenvalues in [0,1] (from MState.le_one and σ.nonneg),
we have σ^r has eigenvalues λ_i^r ∈ [0,1] for r > 0.
Use HermitianMat.le_iff and show (1 - σ^r) is PSD.
Express 1 - σ^r using CFC: 1 - σ^r = σ.M.cfc(fun x => 1 - x^r) (via cfc_sub_apply, rpow_eq_cfc).
Then use cfc_nonneg_iff to reduce to showing 1 - λ_i^r ≥ 0 for each eigenvalue.
Since λ_i ∈ [0,1] (from le_one) and r > 0, this follows from Real.rpow_le_one.
-/
lemma MState.rpow_le_one' {r : ℝ} (hσ : 0 < r) : σ.M ^ r ≤ 1 := by
  rw [HermitianMat.le_iff]
  have h1 : 1 - σ.M ^ r = σ.M.cfc (fun x => 1 - x ^ r) := by
    rw [HermitianMat.rpow_eq_cfc]
    have : σ.M.cfc (fun _ => (1:ℝ)) = 1 := by ext1; simp
    rw [← this, ← HermitianMat.cfc_sub_apply]
  rw [h1, ← HermitianMat.zero_le_iff, HermitianMat.cfc_nonneg_iff]
  intro i
  have hge : 0 ≤ σ.M.H.eigenvalues i :=
    (HermitianMat.zero_le_iff.mp σ.nonneg).eigenvalues_nonneg i
  have hle : σ.M.H.eigenvalues i ≤ 1 := σ.eigenvalue_le_one i
  linarith [Real.rpow_le_one hge hle hσ.le]

/--
For positive A ≤ 1 with Tr[A] ≤ 1 and p ≥ 1, we have Tr[A^p] ≤ Tr[A].
This is because each eigenvalue λ ∈ [0,1] satisfies λ^p ≤ λ for p ≥ 1.
-/
lemma HermitianMat.trace_rpow_le_trace_of_le_one
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    (A ^ p).trace ≤ A.trace := by
  sorry

/-
PROBLEM
Show that for density matrices ρ, σ (PSD with trace 1) and 0 < α < 1,
Tr[(σ^t ρ σ^t)^α] ≤ 1, where t = (1-α)/(2α).

PROVIDED SOLUTION
Step 1: Since ρ ≤ I (density matrix), by conj_mono:
  σ^t ρ σ^t ≤ σ^t I σ^t = σ^{2t}

Step 2: Since σ ≤ I and 2t > 0 (because 0 < α < 1), we have σ^{2t} ≤ I.
  So A := σ^t ρ σ^t ≤ I with all eigenvalues in [0,1].

Step 3: Tr[A] = Tr[σ^{2t} ρ] ≤ Tr[I · ρ] = Tr[ρ] = 1 (using σ^{2t} ≤ I).

Step 4: Since 0 < α < 1 and A ≤ I with Tr[A] ≤ 1, we use trace subadditivity
  (Rotfel'd inequality) on the spectral decomposition of A, combined with the
  scalar Hölder inequality, to conclude Tr[A^α] ≤ 1.

  More precisely, decompose the problem using the spectral decomposition of σ:
  σ^{2t} = Σ_i d_i^{2t} P_i where P_i are rank-1 projectors.
  Then ρ^{1/2} σ^{2t} ρ^{1/2} = Σ_i d_i^{2t} (ρ^{1/2} P_i ρ^{1/2}).
  By trace subadditivity: Tr[(Σ ...)^α] ≤ Σ_i Tr[(d_i^{2t} ρ^{1/2} P_i ρ^{1/2})^α]
    = Σ_i d_i^{2tα} ⟨f_i,ρ f_i⟩^α = Σ_i d_i^{1-α} R_ii^α.
  By scalar Hölder: Σ_i d_i^{1-α} R_ii^α ≤ (Σ d_i)^{1-α} (Σ R_ii)^α = 1.

  Alternatively, since A ≤ I and A ≥ 0, we have Tr[A^α] ≤ 1 by noting that
  the eigenvalues μ_i ∈ [0,1] satisfy: Σ μ_i^α is maximized (subject to
  Σ μ_i ≤ 1 and μ_i ∈ [0,1]) when there is a single nonzero eigenvalue equal to 1,
  giving Σ μ_i^α ≤ 1. This is proved by the Schatten norm monotonicity argument.
-/
private theorem sandwiched_trace_of_lt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace ≤ 1 := by
  -- The sandwiched expression is PSD and ≤ 1
  -- The proof uses Schatten norm theory:
  -- Step 1: A := σ^t ρ σ^t ≤ σ^{2t} ≤ 1 (using conj_mono with ρ ≤ 1, and rpow_le_one')
  -- Step 2: Q_α = ||σ^t ρ^{1/2}||_{2α}^{2α} ≤ ||σ^t||_{1/t}^{2α} · ||ρ^{1/2}||_2^{2α} = 1
  --   (Hölder for Schatten norms with p = 1/t, q = 2, r = 2α)
  sorry

/-
PROBLEM
Show that for density matrices ρ, σ (PSD with trace 1) and α > 1,
Tr[(σ^t ρ σ^t)^α] ≥ 1, where t = (1-α)/(2α).

PROVIDED SOLUTION
Let A = σ^t ρ σ^t (which is PSD). We use the trace Hölder inequality.

Step 1: Show that Tr[A · σ^{-2t}] = Tr[ρ] = 1.
  We have A · σ^{-2t} = σ^t ρ σ^t · σ^{-2t} = σ^t ρ σ^{-t}.
  By cyclicity: Tr[σ^t ρ σ^{-t}] = Tr[σ^{-t} σ^t ρ] = Tr[P_σ ρ] = Tr[ρ] = 1,
  where P_σ is the projection onto σ's support, and P_σ ρ = ρ by the kernel condition.
  Equivalently: ⟪A, σ^{-2t}⟫ = 1.

Step 2: Apply the trace Hölder inequality with p = α, q = α/(α-1):
  ⟪A, σ^{-2t}⟫ ≤ Tr[A^α]^{1/α} · Tr[σ^{-2t·q}]^{1/q}

Step 3: Compute -2t · q = -(1-α)/α · α/(α-1) = (α-1)/α · α/(α-1) = 1.
  So Tr[σ^{-2t·q}] = Tr[σ^1] = Tr[σ] = 1.

Step 4: From 1 ≤ Tr[A^α]^{1/α} · 1, we get Tr[A^α] ≥ 1.
-/
private theorem sandwiched_trace_of_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    1 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  -- A is PSD
  have hA_nonneg : 0 ≤ ρ.M.conj (σ.M ^ ((1 - α)/(2 * α))).mat :=
    HermitianMat.conj_nonneg _ ρ.nonneg
  -- The proof uses the trace Hölder inequality:
  -- Step 1: ⟪A, σ^{-2t}⟫ = Tr[ρ] = 1 (via kernel condition and rpow algebra)
  -- Step 2: By Hölder with p = α, q = α/(α-1):
  --   1 ≤ Tr[A^α]^{1/α} · Tr[σ^{-2t·q}]^{1/q}
  -- Step 3: The exponent -2t·q = 1, so Tr[σ] = 1
  -- Step 4: 1 ≤ Tr[A^α]^{1/α}, hence Tr[A^α] ≥ 1
  sorry

private theorem sandwichedRelRentropy_nonneg_α_lt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα0 : 0 < α) (hα : α < 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  apply div_nonneg_of_nonpos
  · apply Real.log_nonpos
    · exact (sandwiched_trace_pos h).le
    · exact sandwiched_trace_of_lt_1 h hα0 hα
  · linarith

private theorem sandwichedRelRentropy_nonneg_α_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  grw [← sandwiched_trace_of_gt_1 h hα]
  · simp
  · linarith

theorem inner_log_sub_log_nonneg (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  sorry

theorem sandwichedRelRentropy_nonneg {α : ℝ} (hα : 0 < α) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  split_ifs with h1
  · exact inner_log_sub_log_nonneg h
  by_cases hα₂ : α > 1
  · exact sandwichedRelRentropy_nonneg_α_gt_1 h hα₂
  · have : α < 1 := by push_neg at hα₂; exact lt_of_le_of_ne hα₂ h1
    exact sandwichedRelRentropy_nonneg_α_lt_1 h hα this

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. For α ≤ 0, this gives junk value 0. (There
  is no conventional value for α < 0; there is a continuous limit at α = 0, but it is complicated and
  unneeded at the moment.)-/
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if hα : 0 < α then
    if h : σ.M.ker ≤ ρ.M.ker
    then (.ofNNReal ⟨if α = 1 then
        ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else
        ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1),
      sandwichedRelRentropy_nonneg hα h⟩)
    else ⊤
  else 0

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. Also called
the Umegaki quantum relative entropy, when it's necessary to distinguish from other
relative entropies. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

section additivity

--TODO Cleanup. Ugh.

/--
If the kernels of the components are contained, then the kernel of the Kronecker product is contained.
-/
lemma ker_kron_le_of_le {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (A C : Matrix d₁ d₁ ℂ) (B D : Matrix d₂ d₂ ℂ)
    (hA : LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker C.toEuclideanLin)
    (hB : LinearMap.ker B.toEuclideanLin ≤ LinearMap.ker D.toEuclideanLin) :
    LinearMap.ker (A.kronecker B).toEuclideanLin ≤ LinearMap.ker (C.kronecker D).toEuclideanLin := by
  intro x hx
  simp only [Matrix.kronecker, LinearMap.mem_ker, Matrix.toEuclideanLin_apply,
    WithLp.toLp_eq_zero] at hx ⊢
  -- By definition of Kronecker product, we know that $(A \otimes B)x = 0$ if and only if for all $i$ and $j$, $\sum_{k,l} A_{ik} B_{jl} x_{kl} = 0$.
  have h_kronecker : ∀ i j, ∑ k, A i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    replace hx := congr_fun hx ( i, j )
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, PiLp.ofLp_apply,
      Pi.zero_apply, smul_eq_mul, Finset.mul_sum] at hx ⊢
    rw [ ← Finset.sum_product' ]
    simpa only [mul_assoc, Finset.univ_product_univ] using hx
  -- Apply the hypothesis `hA` to each term in the sum.
  have h_apply_hA : ∀ i j, ∑ k, C i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    specialize hA ( show ( fun k => ∑ l, B j l • x ( k, l ) ) ∈ LinearMap.ker ( Matrix.toEuclideanLin A ) from ?_ )
    · simp_all only [smul_eq_mul, LinearMap.mem_ker]
      ext i_1 : 1
      simp_all only [PiLp.zero_apply]
      apply h_kronecker
    · exact congr_fun hA i
  ext ⟨ i, j ⟩
  simp only [smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, PiLp.ofLp_apply,
    Pi.zero_apply] at h_kronecker h_apply_hA ⊢
  have h_apply_hB : ∑ l, D j l • ∑ k, C i k • x (k, l) = 0 := by
    specialize hB
    simp_all only [funext_iff, Pi.zero_apply, Prod.forall, smul_eq_mul]
    have := hB ( show ( fun l => ∑ k, C i k * x ( k, l ) ) ∈ LinearMap.ker ( Matrix.toEuclideanLin B ) from ?_ )
    · simp_all only [LinearMap.mem_ker] ;
      exact congr_fun this j
    · ext j
      specialize h_apply_hA i j
      simp_all [ Matrix.mulVec, dotProduct, Finset.mul_sum ] ;
      convert h_apply_hA using 1
      simp only [Matrix.toEuclideanLin, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply,
        LinearEquiv.symm_symm, WithLp.linearEquiv_apply, Matrix.toLin'_apply,
        WithLp.linearEquiv_symm_apply, PiLp.toLp_apply];
      simp only [Matrix.mulVec, dotProduct, PiLp.ofLp_apply, Finset.mul_sum, mul_left_comm];
      rw [Finset.sum_comm]
  rw [← h_apply_hB]
  simp only [mul_comm, mul_left_comm]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> simp [mul_left_comm ]

--TODO: Generalize to arbitrary PSD matrices.
/--
If the kernel of a product state is contained in another, the left component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_left (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₁.M.ker ≤ ρ₁.M.ker := by
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v : d₂ → ℂ, v ∉ (σ₂ :HermitianMat d₂ ℂ).ker ∧ v ∉ (ρ₂ :HermitianMat d₂ ℂ).ker := by
    have h_union : (σ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ ∧ (ρ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ := by
      constructor <;> intro h_top;
      · have h_contra : σ₂.M = 0 := by
          ext1
          simp_all [ Submodule.eq_top_iff'];
          ext i j; specialize h_top ( EuclideanSpace.single j 1 )
          simp_all
          replace h_top := congr_fun h_top i
          simp_all
          convert h_top using 1;
          erw [ Matrix.toEuclideanLin_apply ] ; aesop;
        exact σ₂.pos.ne' h_contra;
      · have h_contra : ρ₂.M = 0 := by
          ext i j; simp_all [ Submodule.eq_top_iff' ] ;
          convert congr_fun ( h_top ( Pi.single j 1 ) ) i using 1 ; simp
          simp [ HermitianMat.lin ];
          simp [ Matrix.toEuclideanLin, Matrix.mulVec, dotProduct ];
          rw [ Finset.sum_eq_single j ] <;> aesop;
        exact ρ₂.pos.ne' h_contra;
    have h_union : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₂)), U ≠ ⊤ → V ≠ ⊤ → ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∉ V := by
      intros U V hU hV;
      by_contra h_contra;
      have h_union : U ⊔ V = ⊤ := by
        ext v
        simp only [Submodule.mem_top, iff_true]
        by_cases hvU : v ∈ U <;> by_cases hvV : v ∈ V <;> simp_all [ Submodule.mem_sup ];
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ 0, by simp, v, h_contra v hvU, by simp ⟩;
      have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∈ V := by
        have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∈ V ∧ v ∉ U := by
          have h_not_subset : ¬V ≤ U := by
            exact fun h => hU <| by rw [ eq_top_iff ] ; exact h_union ▸ sup_le ( by tauto ) h;
          exact Set.not_subset.mp h_not_subset;
        exact ⟨ h_union.choose, h_union.choose_spec.2, h_union.choose_spec.1 ⟩;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_union;
      obtain ⟨ w, hw₁, hw₂ ⟩ : ∃ w : EuclideanSpace ℂ d₂, w ∉ V ∧ w ∈ U := by
        obtain ⟨ w, hw ⟩ := ( show ∃ w : EuclideanSpace ℂ d₂, w ∉ V from by simpa [ Submodule.eq_top_iff' ] using hV ) ; use w; simp_all [ Submodule.eq_top_iff' ] ;
        exact Classical.not_not.1 fun hw' => hw <| h_contra _ hw';
      have h_union : v + w ∉ U ∧ v + w ∉ V := by
        exact ⟨ fun h => hv₁ <| by simpa using U.sub_mem h hw₂, fun h => hw₁ <| by simpa using V.sub_mem h hv₂ ⟩;
      exact h_contra ⟨ v + w, h_union.1, h_union.2 ⟩;
    exact h_union _ _ ( by tauto ) ( by tauto );
  -- Consider $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := fun p => u p.1 * v p.2;
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    ext ⟨i, j⟩
    simp [z]
    have h_kronecker : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ) (u : d₁ → ℂ) (v : d₂ → ℂ), (A.kronecker B).mulVec (fun p => u p.1 * v p.2) = fun p => (A.mulVec u) p.1 * (B.mulVec v) p.2 := by
      intro A B u v; ext ⟨ i, j ⟩ ; simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm ] ;
      exact Fintype.sum_prod_type_right fun x => A i x.1 * (B j x.2 * (u x.1 * v x.2));
    convert congr_fun ( h_kronecker σ₁.1.mat σ₂.1.mat u v ) ( i, j ) using 1 ; simp
    exact Or.inl ( by simpa [ Matrix.mulVec ] using congr_fun hu i );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    exact h hz;
  have hz'' : ∀ a b, (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = 0 := by
    intro a b
    have hz'' : (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = ((ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).val.mulVec z) (a, b) := by
      simp [ Matrix.mulVec, dotProduct];
      simp [  Finset.sum_mul, mul_assoc, mul_comm];
      simp [ z, Finset.mul_sum, mul_assoc, mul_left_comm ];
      erw [ Finset.sum_product ] ; simp
      exact rfl;
    exact hz''.trans ( by simpa using congr_fun hz' ( a, b ) );
  ext a; specialize hz'' a; simp_all [ Matrix.mulVec, dotProduct ] ;
  contrapose! hv;
  intro hv'; ext b; specialize hz'' b; simp_all
  exact hz''.resolve_left ( by simpa [ Matrix.mulVec, dotProduct ] using hv )


--TODO: Generalize to arbitrary PSD matrices.
--TODO: Rewrite the proof using the `ker_le_of_ker_kron_le_left` lemma, and the fact that
-- there's a unitary whose conjugation swaps the kronecker product.
/--
If the kernel of a product state is contained in another, the right component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_right (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₂.M.ker ≤ ρ₂.M.ker := by
  intro v hv;
  have h_z : ∃ u : EuclideanSpace ℂ d₁, u ≠ 0 ∧ u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
    have h_z : σ₁.M.ker ≠ ⊤ ∧ ρ₁.M.ker ≠ ⊤ := by
      have h_ker_ne_top : ∀ (ρ : MState d₁), ρ.M.ker ≠ ⊤ := by
        intro ρ hρ_top
        have h_contra : ρ.M = 0 := by
          ext i j
          simp_all [ Submodule.eq_top_iff' ] ;
          convert congr_fun ( hρ_top ( EuclideanSpace.single j 1 ) ) i using 1
          simp
          erw [ Matrix.toEuclideanLin_apply ] ; aesop;
        exact ρ.pos.ne' h_contra;
      exact ⟨ h_ker_ne_top σ₁, h_ker_ne_top ρ₁ ⟩;
    have h_z : ∃ u : EuclideanSpace ℂ d₁, u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
      have h_z : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₁)), U ≠ ⊤ → V ≠ ⊤ → ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∉ V := by
        intro U V hU hV
        by_contra h_contra
        push_neg at h_contra;
        have h_union : ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∈ V := by
          exact Exists.elim ( show ∃ u : EuclideanSpace ℂ d₁, u ∉ U from by simpa [ Submodule.eq_top_iff' ] using hU ) fun u hu => ⟨ u, hu, h_contra u hu ⟩;
        obtain ⟨ u, hu₁, hu₂ ⟩ := h_union;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v + u ∈ V := by
          intro v hv; specialize h_contra ( v + u ) ; simp_all [ Submodule.add_mem_iff_right ] ;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v ∈ V := by
          exact fun v hv => by simpa using V.sub_mem ( h_union v hv ) hu₂;
        exact hV ( eq_top_iff.mpr fun x hx => by by_cases hxU : x ∈ U <;> aesop );
      exact h_z _ _ ( by tauto ) ( by tauto );
    exact ⟨ h_z.choose, by intro h; simpa [ h ] using h_z.choose_spec.1, h_z.choose_spec.1, h_z.choose_spec.2 ⟩;
  obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := h_z;
  -- Consider the vector $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := fun p => u p.1 * v p.2;
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂).M.ker := by
    -- By definition of $z$, we have $(σ₁ ⊗ σ₂).mat.mulVec z = σ₁.mat.mulVec u ⊗ σ₂.mat.mulVec v$.
    have hz_mul : (σ₁ ⊗ᴹ σ₂).M.mat.mulVec z = fun p => (σ₁.M.mat.mulVec u) p.1 * (σ₂.M.mat.mulVec v) p.2 := by
      ext p; simp [z, Matrix.mulVec]
      simp [ dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp;
      exact fun a b => Or.inl <| Or.inl <| rfl;
    simp_all [ funext_iff, Matrix.mulVec ];
    ext ⟨ a, b ⟩ ; specialize hz_mul a b
    simp_all [ dotProduct] ;
    convert hz_mul using 1;
    simp_all only [zero_eq_mul]
    exact Or.inr ( by simpa [ Matrix.mulVec, dotProduct ] using congr_fun hv b );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
    exact h hz;
  have hz'' : ∀ i j, (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j = 0 := by
    intro i j;
    have hz'' : (ρ₁.M.val.kronecker ρ₂.M.val).mulVec (fun p => u p.1 * v p.2) (i, j) = (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j := by
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm ];
      simp [ mul_assoc, Finset.mul_sum, Finset.sum_mul ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp;
      exact fun _ _ => Or.inl <| Or.inl rfl;
    exact hz''.symm.trans ( by simpa using congr_fun hz' ( i, j ) );
  contrapose! hz'';
  obtain ⟨ i, hi ⟩ := Function.ne_iff.mp ( show ρ₁.M.val.mulVec u ≠ 0 from fun h => hu₃ <| by simpa [ h ] )
  obtain ⟨ j, hj ⟩ := Function.ne_iff.mp ( show ρ₂.M.val.mulVec v ≠ 0 from fun h => hz'' <| by simpa [ h ] )
  use i, j
  aesop;

/--
The kernel of a product state is contained in another product state's kernel iff the individual
kernels are contained.
-/
lemma ker_prod_le_iff (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker ↔ σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker := by
  constructor <;> intro h;
  · exact ⟨ ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h, ker_le_of_ker_kron_le_right ρ₁ σ₁ ρ₂ σ₂ h ⟩;
  · convert ker_kron_le_of_le _ _ _ _ h.1 h.2 using 1

--TODO: Generalize to RCLike.
omit [DecidableEq d₁] [DecidableEq d₂] in
lemma HermitianMat.inner_kron
    (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ) (C : HermitianMat d₁ ℂ) (D : HermitianMat d₂ ℂ) :
    ⟪A ⊗ₖ B, C ⊗ₖ D⟫ = ⟪A, C⟫ * ⟪B, D⟫ := by
  -- Apply the property of the trace of Kronecker products.
  have h_trace_kron : ∀ (A₁ B₁ : Matrix d₁ d₁ ℂ) (A₂ B₂ : Matrix d₂ d₂ ℂ), Matrix.trace (Matrix.kroneckerMap (· * ·) A₁ A₂ * Matrix.kroneckerMap (· * ·) B₁ B₂) = Matrix.trace (A₁ * B₁) * Matrix.trace (A₂ * B₂) := by
    intro A₁ B₁ A₂ B₂
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp_all only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, kronecker_mat, RCLike.mul_re,
    RCLike.re_to_complex, RCLike.im_to_complex, sub_eq_self, mul_eq_zero];
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.im_sum,
    Complex.mul_im];
  left;
  have h_symm : ∀ x x_1, (A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re = -((A x_1 x).re * (C x x_1).im + (A x_1 x).im * (C x x_1).re) := by
    intro x y; have := congr_fun ( congr_fun A.2 y ) x; have := congr_fun ( congr_fun C.2 y ) x; simp_all [ Complex.ext_iff ] ;
    grind;
  have h_sum_zero : ∑ x, ∑ x_1, ((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) = ∑ x, ∑ x_1, -((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) := by
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => h_symm _ _ ▸ rfl;
  norm_num [ Finset.sum_add_distrib ] at * ; linarith

lemma HermitianMat.supportProj_mul_self (A : HermitianMat d ℂ) :
    A.supportProj.mat * A.mat = A.mat := by
  have h_supportProj_mul_A : ∀ (v : d → ℂ), (A.supportProj.val.mulVec (A.val.mulVec v)) = (A.val.mulVec v) := by
    intro v
    have h_range : A.val.mulVec v ∈ LinearMap.range A.val.toEuclideanLin := by
      exact ⟨ v, rfl ⟩
    have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), v ∈ LinearMap.range A.val.toEuclideanLin → (A.supportProj.val.toEuclideanLin v) = v := by
      intro v hv
      have h_supportProj_mul_A : (A.supportProj.val.toEuclideanLin v) = (Submodule.orthogonalProjection (LinearMap.range A.val.toEuclideanLin) v) := by
        simp only [Matrix.toEuclideanLin, supportProj, val_eq_coe, LinearEquiv.trans_apply,
          LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, WithLp.linearEquiv_apply,
          Matrix.toLin'_apply, WithLp.linearEquiv_symm_apply,
          Submodule.coe_orthogonalProjection_apply];
        simp only [projector, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL, mat_mk];
        simp only [LinearMap.toMatrix, OrthonormalBasis.coe_toBasis_repr, LinearEquiv.trans_apply,
          LinearMap.toMatrix'_mulVec, LinearEquiv.arrowCongr_apply, LinearMap.comp_apply,
          ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
          Submodule.coe_orthogonalProjection_apply];
        exact rfl
      rw [h_supportProj_mul_A]
      exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (by simpa using hv) (by simp)
    convert h_supportProj_mul_A _ h_range using 1;
  exact Matrix.toLin'.injective ( LinearMap.ext fun v => by simpa using h_supportProj_mul_A v )

lemma HermitianMat.inner_supportProj_self (A : HermitianMat d ℂ) :
    ⟪A, A.supportProj⟫ = A.trace := by
  simp only [trace, IsMaximalSelfAdjoint.RCLike_selfadjMap, Matrix.trace, Matrix.diag_apply,
    mat_apply, map_sum, RCLike.re_to_complex]
  simp only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, RCLike.re_to_complex];
  convert congr_arg Complex.re ( congr_arg Matrix.trace ( HermitianMat.supportProj_mul_self A ) ) using 1;
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.re_sum,
      Complex.mul_re, Finset.sum_sub_distrib, mul_comm];
    exact congrArg₂ _ ( Finset.sum_comm ) ( Finset.sum_comm );
  · simp only [Matrix.trace, Matrix.diag_apply, mat_apply, Complex.re_sum]

lemma HermitianMat.mul_supportProj_of_ker_le (A B : HermitianMat d ℂ)
  (h : LinearMap.ker B.lin ≤ LinearMap.ker A.lin) :
    A.mat * B.supportProj.mat = A.mat := by
  -- Since $B.supportProj$ is the projection onto $range B$, we have $B.supportProj * B.mat = B.mat$.
  have h_supportProj_mul_B : B.supportProj.mat * B.mat = B.mat := by
    exact supportProj_mul_self B;
  have h_range_A_subset_range_B : LinearMap.range A.lin ≤ LinearMap.range B.lin := by
    have h_orthogonal_complement : LinearMap.range (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = (LinearMap.ker (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      have h_orthogonal_complement : ∀ (T : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d), T = T.adjoint → LinearMap.range T = (LinearMap.ker T)ᗮ := by
        intro T hT;
        refine' Submodule.eq_of_le_of_finrank_eq _ _;
        · intro x hx
          obtain ⟨y, hy⟩ := hx
          have h_orthogonal : ∀ z ∈ LinearMap.ker T, inner ℂ x z = 0 := by
            intro z hz
            have h_orthogonal : inner ℂ (T y) z = inner ℂ y (T.adjoint z) := by
              rw [ LinearMap.adjoint_inner_right ];
            simp [ ← hT ] at h_orthogonal ⊢
            aesop ( simp_config := { singlePass := true } );
          exact (Submodule.mem_orthogonal' (LinearMap.ker T) x).mpr h_orthogonal;
        · have := LinearMap.finrank_range_add_finrank_ker T;
          have := Submodule.finrank_add_finrank_orthogonal ( LinearMap.ker T );
          linarith;
      apply h_orthogonal_complement;
      ext
      simp
    have h_orthogonal_complement_A : LinearMap.range (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) ≤ (LinearMap.ker (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      intro x hx;
      intro y hy
      simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, LinearMap.mem_ker]
      obtain ⟨ z, rfl ⟩ := hx;
      have h_orthogonal_complement_A : ∀ (y z : EuclideanSpace ℂ d), ⟪y, A.lin z⟫_ℂ = ⟪A.lin y, z⟫_ℂ := by
        simp
      rw [ h_orthogonal_complement_A, hy, inner_zero_left ];
    exact h_orthogonal_complement.symm ▸ le_trans h_orthogonal_complement_A ( Submodule.orthogonal_le h );
  -- Since $B.supportProj$ is the projection onto $range B$, and $range A \subseteq range B$, we have $B.supportProj * A = A$.
  have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), B.supportProj.mat.mulVec (A.mat.mulVec v) = A.mat.mulVec v := by
    intro v
    have hv_range_B : A.mat.mulVec v ∈ LinearMap.range B.lin := by
      exact h_range_A_subset_range_B ( Set.mem_range_self v );
    obtain ⟨ w, hw ⟩ := hv_range_B;
    replace h_supportProj_mul_B := congr_arg ( fun m => m.mulVec w ) h_supportProj_mul_B
    simpa only [← hw, ← Matrix.mulVec_mulVec] using h_supportProj_mul_B
  -- By definition of matrix multiplication, if B.supportProj * A * v = A * v for all vectors v, then B.supportProj * A = A.
  have h_matrix_eq : ∀ (M N : Matrix d d ℂ), (∀ v : EuclideanSpace ℂ d, M.mulVec (N.mulVec v) = N.mulVec v) → M * N = N := by
    intro M N hMN; ext i j; specialize hMN ( Pi.single j 1 ) ; replace hMN := congr_fun hMN i; aesop;
  apply_fun Matrix.conjTranspose at *; aesop;
  exact fun M N hMN => by simpa using congr_arg Matrix.conjTranspose hMN;

lemma HermitianMat.inner_supportProj_of_ker_le (A B : HermitianMat d ℂ)
  (h : LinearMap.ker B.lin ≤ LinearMap.ker A.lin) :
    ⟪A, B.supportProj⟫ = A.trace := by
  rw [inner_def, mul_supportProj_of_ker_le A B h, trace]

attribute [fun_prop] ContinuousAt.rpow

lemma continuousOn_rpow_uniform {K : Set ℝ} (hK : IsCompact K) :
    ContinuousOn (fun r : ℝ ↦ UniformOnFun.ofFun {K} (fun t : ℝ ↦ t ^ r)) (Set.Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun r hr => ?_
  rw [Set.mem_Ioi] at hr
  apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, Metric.tendstoUniformlyOn_iff,
    Function.comp_apply, forall_eq]
  intro ε hεpos;
  have h_unif_cont : UniformContinuousOn (fun (p : ℝ × ℝ) => p.1 ^ p.2) (K ×ˢ Set.Icc (r / 2) (r * 2)) := by
    apply IsCompact.uniformContinuousOn_of_continuous
    · exact hK.prod CompactIccSpace.isCompact_Icc
    · refine continuousOn_of_forall_continuousAt fun p ⟨hp₁, ⟨hp₂₁, hp₂₂⟩⟩ ↦ ?_
      have _ : p.1 ≠ 0 ∨ 0 < p.2 := by right; linarith
      fun_prop (disch := assumption)
  rw [Metric.uniformContinuousOn_iff] at h_unif_cont
  obtain ⟨δ, hδpos, H⟩ := h_unif_cont ε hεpos
  filter_upwards [Ioo_mem_nhds (show r / 2 < r by linarith) (show r < r * 2 by linarith), Ioo_mem_nhds (show r - δ < r by linarith) (show r < r + δ by linarith)] with n ⟨_, _⟩ ⟨_, _⟩ x hx
  refine H (x, r) ⟨hx, ?_⟩ (x, n) ⟨hx, ?_⟩ ?_
  · constructor <;> linarith
  · constructor <;> linarith
  · have : |r - n| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa

theorem sandwichedRelRentropy_additive_alpha_one_aux (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h1 : σ₁.M.ker ≤ ρ₁.M.ker) (h2 : σ₂.M.ker ≤ ρ₂.M.ker) :
    ⟪(ρ₁ ⊗ᴹ ρ₂).M, (ρ₁ ⊗ᴹ ρ₂).M.log - (σ₁ ⊗ᴹ σ₂).M.log⟫ =
    ⟪ρ₁.M, ρ₁.M.log - σ₁.M.log⟫_ℝ + ⟪ρ₂.M, ρ₂.M.log - σ₂.M.log⟫ := by
  have h_log_kron : (ρ₁ ⊗ᴹ ρ₂).M.log = ρ₁.M.log ⊗ₖ ρ₂.M.supportProj + ρ₁.M.supportProj ⊗ₖ ρ₂.M.log ∧ (σ₁ ⊗ᴹ σ₂).M.log = σ₁.M.log ⊗ₖ σ₂.M.supportProj + σ₁.M.supportProj ⊗ₖ σ₂.M.log := by
    constructor <;> apply HermitianMat.log_kron_with_proj;
  have h_inner_supportProj : ∀ (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ), ⟪A ⊗ₖ B, ρ₁ ⊗ᴹ ρ₂⟫ = ⟪A, ρ₁⟫ * ⟪B, ρ₂⟫ := by
    exact fun A B => HermitianMat.inner_kron A B ρ₁ ρ₂;
  simp only [HermitianMat.ker] at h1 h2
  simp_all only [inner_sub_right, inner_add_right, real_inner_comm,
    HermitianMat.inner_supportProj_self, MState.tr, mul_one, one_mul,
    HermitianMat.inner_supportProj_of_ker_le]
  abel

/--
The Sandwiched Renyi Relative entropy is additive for α=1 (standard relative entropy).
-/
private theorem sandwichedRelRentropy_additive_alpha_one (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ 1(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ 1(ρ₁‖σ₁) + D̃_ 1(ρ₂‖σ₂) := by
  by_cases h1 : σ₁.M.ker ≤ ρ₁.M.ker
  <;> by_cases h2 : σ₂.M.ker ≤ ρ₂.M.ker
  · simp only [SandwichedRelRentropy, ↓reduceIte, ↓reduceDIte, h1, h2]
    split_ifs <;> simp_all [ ker_prod_le_iff ];
    simp only [sandwichedRelRentropy_additive_alpha_one_aux ρ₁ σ₁ ρ₂ σ₂ h1 h2]
    rfl
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      add_top, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    have := ker_prod_le_iff ρ₁ σ₁ ρ₂ σ₂
    tauto
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      top_add, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    contrapose! h1
    exact (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂) h1
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      add_top, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    contrapose! h1
    exact (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂) h1

@[simp]
lemma HermitianMat.rpow_zero (A : HermitianMat d 𝕜) : A ^ (0 : ℝ) = 1 := by
  simp [rpow_eq_cfc]

open scoped Kronecker in
omit [DecidableEq d₁] [DecidableEq d₂] in
lemma HermitianMat.conj_kron
  (A : Matrix d₁ d₁ 𝕜) (B : Matrix d₂ d₂ 𝕜) (C : HermitianMat d₁ 𝕜) (D : HermitianMat d₂ 𝕜) :
    conj (A ⊗ₖ B) (C ⊗ₖ D) = conj A C ⊗ₖ conj B D := by
  ext1
  simp [conj, Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker]

lemma HermitianMat.rpow_diagonal (a : d → ℝ) (r : ℝ) :
  (diagonal ℂ a) ^ r = diagonal ℂ (fun i => a i ^ r) := by
    exact HermitianMat.cfc_diagonal _ _

private lemma HermitianMat.pow_kron_diagonal
    (a : d₁ → ℝ) (b : d₂ → ℝ) (r : ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) :
    ((HermitianMat.diagonal ℂ a) ⊗ₖ (HermitianMat.diagonal ℂ b)) ^ r =
    ((HermitianMat.diagonal ℂ a) ^ r) ⊗ₖ ((HermitianMat.diagonal ℂ b) ^ r) := by
  simp only [HermitianMat.kronecker_diagonal, HermitianMat.rpow_diagonal]
  congr! 2 with x
  apply Real.mul_rpow (ha x.1) (hb x.2)

open scoped Kronecker Matrix in
lemma HermitianMat.pow_kron
    {A : HermitianMat d₁ ℂ} {B : HermitianMat d₂ ℂ} (r : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A ⊗ₖ B) ^ r = (A ^ r) ⊗ₖ (B ^ r) := by
  obtain ⟨U, a, ha, hA⟩ : ∃ U : 𝐔[d₁], ∃ a : d₁ → ℝ, (∀ i, 0 ≤ a i) ∧ A = conj U.val (diagonal ℂ a) := by
    rw [zero_le_iff] at hA
    exact ⟨_, _, hA.eigenvalues_nonneg, eq_conj_diagonal A⟩
  obtain ⟨V, b, hb, hB⟩ : ∃ V : 𝐔[d₂], ∃ b : d₂ → ℝ, (∀ j, 0 ≤ b j) ∧ B = conj V.val (diagonal ℂ b) := by
    rw [zero_le_iff] at hB
    exact ⟨_, _, hB.eigenvalues_nonneg, eq_conj_diagonal B⟩
  have h_kron_r_pow : (A ⊗ₖ B) ^ r = conj (U ⊗ᵤ V).val ((diagonal ℂ a ⊗ₖ diagonal ℂ b) ^ r) := by
    subst hB hA
    rw [← rpow_conj_unitary, Matrix.unitary_kron, conj_kron]
  rw [h_kron_r_pow]
  subst A B
  have h_kron_r_pow_diag : (diagonal ℂ a ⊗ₖ diagonal ℂ b) ^ r = ((diagonal ℂ a) ^ r) ⊗ₖ ((diagonal ℂ b) ^ r) := by
    exact pow_kron_diagonal a b r ha hb
  rw [h_kron_r_pow_diag, Matrix.unitary_kron]
  rw [rpow_conj_unitary, rpow_conj_unitary, ← conj_kron]

lemma sandwiched_term_product (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) (α β : ℝ) :
    (((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ β).mat) ^ α).trace =
    ((ρ₁.M.conj (σ₁.M ^ β).mat) ^ α).trace * ((ρ₂.M.conj (σ₂.M ^ β).mat) ^ α).trace := by
  simp only [MState.prod]
  rw [← HermitianMat.trace_kronecker]
  rw [← HermitianMat.pow_kron α ?_ ?_, ← HermitianMat.conj_kron,
    HermitianMat.pow_kron β σ₁.nonneg σ₂.nonneg, HermitianMat.kronecker_mat]
  · exact HermitianMat.conj_nonneg _ ρ₁.nonneg
  · exact HermitianMat.conj_nonneg _ ρ₂.nonneg

/-
The Sandwiched Renyi Relative entropy is additive for alpha != 1.
-/
theorem sandwichedRelRentropy_additive_alpha_ne_one {α : ℝ} (hα : α ≠ 1) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  by_cases hα0 : 0 < α; swap
  · simp [SandwichedRelRentropy, hα0]
  by_cases h_ker : σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker
  · simp_all [SandwichedRelRentropy]
    -- Apply the additivity of the trace term to split the logarithm into the sum of the logarithms.
    have h_trace_add : Real.log ((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ ((1 - α) / (2 * α))).mat ^ α).trace = Real.log ((ρ₁.M.conj (σ₁.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace + Real.log ((ρ₂.M.conj (σ₂.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
      rw [ sandwiched_term_product, Real.log_mul ];
      · exact (sandwiched_trace_pos h_ker.1).ne'
      · exact (sandwiched_trace_pos h_ker.2).ne'
    split_ifs <;> simp_all
    · norm_num [ add_div ];
      exact rfl;
    · exact False.elim ( ‹¬ ( σ₁ ⊗ᴹ σ₂ |> MState.M |> HermitianMat.ker ) ≤ ( ρ₁ ⊗ᴹ ρ₂ |> MState.M |> HermitianMat.ker ) › ( by simpa [ HermitianMat.ker ] using ker_prod_le_iff _ _ _ _ |>.2 h_ker ) );
  · have h_ker_prod : ¬((σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) := by
      simp_all  [ ker_prod_le_iff ]
    rw [not_and_or] at h_ker
    rcases h_ker with h_ker | h_ker
    · simp [SandwichedRelRentropy, h_ker_prod, h_ker, hα0]
    · simp [SandwichedRelRentropy, h_ker_prod, h_ker, hα0]

end additivity

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  rcases eq_or_ne α 1 with rfl | hα
  · exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂
  · apply sandwichedRelRentropy_additive_alpha_ne_one hα

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  --or `simp [SandwichedRelRentropy]`.
  exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂

@[simp]
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  rw! [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp [HermitianMat.conj_submatrix]

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp? [SandwichedRelRentropy, NNReal.eq_iff] says
    simp only [SandwichedRelRentropy, hα, ↓reduceDIte, le_refl, sub_self, inner_zero_right,
    ENNReal.coe_eq_zero, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero, ite_eq_left_iff,
    div_eq_zero_iff, Real.log_eq_zero]
  intro hα
  left; right; left
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.rpow_eq_cfc]
  nth_rw 2 [← HermitianMat.cfc_id ρ.M]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp]
  conv =>
    enter [1, 1]
    equals ρ.M.cfc id =>
      apply HermitianMat.cfc_congr_of_nonneg ρ.nonneg
      intro i (hi : 0 ≤ i)
      simp
      rw [← Real.rpow_mul_natCast hi, ← Real.rpow_one_add' hi]
      · rw [← Real.rpow_mul hi]
        field_simp
        ring_nf
        exact Real.rpow_one i
      · field_simp; ring_nf; positivity
  simp

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  by_cases 0 < α
  · simp [SandwichedRelRentropy, HermitianMat.nonSingular_ker_bot, *]
  · simp [SandwichedRelRentropy, *]

@[fun_prop]
lemma continuousOn_exponent : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 0) := by
  fun_prop (disch := intros; linarith [Set.mem_Ioi.mp ‹_›])

@[fun_prop]
lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
    ContinuousOn (fun r : ℝ => z ^ (r : ℂ)) (Set.Ioi 0) := by
  apply ContinuousOn.const_cpow (f := Complex.ofReal)
  · fun_prop
  · grind [ofReal_ne_zero]

/--
The function α ↦ (1 - α) / (2 * α) maps the interval (1, ∞) to (-∞, 0).
-/
lemma maps_to_Iio_of_Ioi_1 : Set.MapsTo (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) (Set.Iio 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rw [Set.mem_Iio]
  have h1 : 1 - x < 0 := by linarith
  have h2 : 0 < 2 * x := by linarith
  exact div_neg_of_neg_of_pos h1 h2

--PR'ed: #35494
@[simp]
theorem frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (p : X) : frontier {p} = {p} := by
  simp [frontier]

private theorem sandwichedRelRentropy.continuousOn_Ioi_1 (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 1) := by
  dsimp [SandwichedRelRentropy]
  split_ifs with hρ
  · simp [← ENNReal.ofReal_eq_coe_nnreal]
    rw [continuousOn_congr (f := fun α ↦ ENNReal.ofReal
      (Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)))]
    · apply (ENNReal.continuous_ofReal).comp_continuousOn
      apply ContinuousOn.div₀
      · apply ContinuousOn.log
        · apply HermitianMat.trace_Continuous.comp_continuousOn
          simp only [HermitianMat.conj, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          sorry
        · intro x hx
          apply LT.lt.ne'
          grw [← sandwiched_trace_of_gt_1 hρ hx]
          exact zero_lt_one
      · fun_prop
      · clear hρ; grind
    · intro α (hα : 1 < α)
      dsimp only
      rw [if_pos (zero_lt_one.trans hα), if_neg hα.ne']
  · rw [continuousOn_congr (f := fun α ↦ ⊤)]
    · fun_prop
    · clear ρ σ hρ;
      grind only [→ Set.EqOn.eq_of_mem, = Set.mem_Ioi, Set.EqOn, cases Or]

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[≠] 1).tendsto (f 1)`.
  sorry

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, EReal.coe_nnreal_eq_coe_real]

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h, qRelativeEnt, SandwichedRelRentropy]

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [SandwichedRelRentropy]

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

@[gcongr]
theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

--BACKPORT
private theorem lowerSemicontinuous_iff {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [Preorder β] {f : α → β} :
    LowerSemicontinuous f ↔ ∀ (x : α), LowerSemicontinuousAt f x := by
  rfl

lemma lowerSemicontinuous_inner (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker):
    LowerSemicontinuousAt (fun x ↦ ⟪ρ.M, x.M.log⟫) x := by
  sorry

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ⟪ρ.M, ρ.M.log - x'.M.log⟫ else ⊤ : EReal) := by
  sorry

/-- Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain. -/
@[fun_prop]
theorem qRelativeEnt.lowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  simp_rw [qRelativeEnt, SandwichedRelRentropy, if_true, lowerSemicontinuous_iff]
  simp only [zero_lt_one, ↓reduceDIte]
  intro x
  by_cases hx : x.M.ker ≤ ρ.M.ker
  · have h₂ := lowerSemicontinuous_inner ρ x hx
    sorry
  · intro y hy
    simp only [hx, ↓reduceDIte] at hy ⊢
    have h₂ := qRelativeEnt_lowerSemicontinuous_2 ρ x hx y hy
    filter_upwards [h₂] with x' hx'
    split_ifs with h₁ junk
    · simpa [← EReal.coe_ennreal_lt_coe_ennreal_iff, h₁] using hx'
    · simp at junk
    · exact hy

/-- Joint convexity of Quantum relative entropy. We can't state this with `ConvexOn` because that requires
an `AddCommMonoid`, which `MState`s are not. Instead we state it with `Mixable`.

TODO:
 * Add the `Mixable` instance that infers from the `Coe` so that the right hand side can be written as
`p [𝐃(ρ₁‖σ₁) ↔ 𝐃(ρ₂‖σ₂)]`
 * Define (joint) convexity as its own thing - a `ConvexOn` for `Mixable` types.
 * Maybe, more broadly, find a way to make `ConvexOn` work with the subset of `Matrix` that corresponds to `MState`.
-/
theorem qRelativeEnt_joint_convexity :
  ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
    𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  sorry

@[simp]
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) : EReal) := by
  sorry

theorem qRelEntropy_le_add_of_le_smul (ρ : MState d) {σ₁ σ₂ : MState d} (hσ : σ₁.M ≤ α • σ₂.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log α)
    := by
  sorry

/-- "Formula for conversion from operator inequality to quantum relative entropy",
-- Proposition S17 of https://arxiv.org/pdf/2401.01926v2 -/
theorem qRelativeEnt_op_le {ρ σ : MState d} (hpos : 0 < α) (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ ENNReal.ofReal (Real.log α) := by
  sorry
