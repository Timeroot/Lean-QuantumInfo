/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.Majorization

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Schatten norms

-/

noncomputable section

/--
The Schatten p-norm of a matrix A is (Tr[(A*A)^(p/2)])^(1/p).
-/
noncomputable def schattenNorm (A : Matrix d d ℂ) (p : ℝ) : ℝ :=
  RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace ^ (1/p)

/-
For a positive Hermitian matrix A, ||A||_p = (Tr(A^p))^(1/p).
-/
theorem schattenNorm_hermitian_pow {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) :
    schattenNorm A.mat p = (A ^ p).trace ^ (1/p) := by
  convert congr_arg (· ^ (1 / p)) _ using 1
  convert congr_arg _ (A.cfc_sq_rpow_eq_cfc_rpow hA p hp) using 1
  unfold HermitianMat.trace
  convert rfl
  convert (A ^ 2).mat_cfc (· ^ (p / 2))
  ext
  simp only [HermitianMat.conjTranspose_mat, HermitianMat.mat_pow]
  convert rfl using 2
  rw [sq]
  exact Matrix.IsHermitian.cfc_eq _ _

lemma schattenNorm_nonneg (A : Matrix d d ℂ) (p : ℝ) :
    0 ≤ schattenNorm A p := by
  by_cases hp : p = 0 <;> simp +decide [ *, schattenNorm ];
  by_cases h₁ : 0 ≤ RCLike.re ( Matrix.trace ( Matrix.IsHermitian.cfc ( Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose ) fun x => x ^ ( p / 2 ) ) ) <;> simp_all +decide [ Real.rpow_nonneg ];
  contrapose! h₁; simp_all +decide [ Matrix.trace ] ; ring_nf; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  refine' Finset.sum_nonneg fun i _ => _ ; norm_num [ Matrix.IsHermitian.cfc ] ; ring_nf ; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  simp +decide [ Matrix.mul_apply, Matrix.diagonal ] ; ring_nf ; norm_num [ Real.exp_nonneg, Real.log_nonneg ] ; (
  exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_nonneg ( sq_nonneg _ ) ( Real.rpow_nonneg (
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _) _ ) ) ( mul_nonneg ( Real.rpow_nonneg (
    Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _) _ ) ( sq_nonneg _ ) ))));

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

/-! ## Relating schattenNorm to singular values -/

/-
PROBLEM
The trace of cfc(A†A, t ↦ t^{p/2}) expressed as a sum of eigenvalues.

PROVIDED SOLUTION
Use Matrix.IsHermitian.cfc_eq to convert cfc to Matrix.IsHermitian.cfc, which is defined as U * diagonal(f(eigenvalues)) * U*. The trace of U * D * U* = trace(D) = ∑ f(eigenvalues i).

More specifically, use Matrix.IsHermitian.trace_eq_sum_eigenvalues on the CFC result, combined with the fact that the eigenvalues of cfc(H, f) are f(eigenvalues of H). The existing lemma HermitianMat.trace_cfc_eq might help, but we need the Matrix version.

Actually, look at Matrix.IsHermitian.cfc: it's defined as eigenvectorUnitary * diagonal(ofReal ∘ f ∘ eigenvalues) * star eigenvectorUnitary. The trace of this is ∑ ofReal(f(eigenvalues i)). Taking re gives ∑ f(eigenvalues i).

So: unfold Matrix.IsHermitian.cfc, compute the trace as Matrix.trace of U D U* = Matrix.trace D (by trace_mul_comm), then Matrix.trace (diagonal g) = ∑ g i, and take re of ∑ ofReal(x) = ∑ x.
-/
lemma schattenNorm_trace_as_eigenvalue_sum (A : Matrix d d ℂ) (p : ℝ) :
    RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace =
    ∑ i : d, ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i) ^ (p/2) := by
  rw [ Matrix.IsHermitian.cfc ];
  simp [ Matrix.trace_mul_comm, Matrix.mul_assoc ]

/-
PROBLEM
For nonneg eigenvalue λ and p > 0, (√λ)^p = λ^{p/2}.

PROVIDED SOLUTION
We have √y = y^{1/2} (by Real.sqrt_eq_rpow). So (√y)^p = (y^{1/2})^p = y^{(1/2)·p} = y^{p/2} by Real.rpow_mul (since y ≥ 0). Use rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hy]; ring_nf.
-/
lemma sqrt_rpow_eq_rpow_half {y p : ℝ} (hy : 0 ≤ y) (_hp : 0 < p) :
    Real.sqrt y ^ p = y ^ (p / 2) := by
  rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul hy ] ; ring_nf

/-
PROBLEM
The Schatten p-norm raised to the p-th power equals the sum of singular values
    raised to the p-th power: `‖A‖_p^p = ∑ σᵢ(A)^p`.

PROVIDED SOLUTION
The proof combines three key facts:

1. schattenNorm A p ^ p = re(Tr[cfc(A†A, t ↦ t^{p/2})]).
   From the definition: schattenNorm A p = (re Tr[...])^{1/p}, so schattenNorm^p = ((re Tr[...])^{1/p})^p. Use ← Real.rpow_mul (with nonneg base) to get exponent 1/p · p = 1, then Real.rpow_one.

2. re(Tr[cfc(A†A, t ↦ t^{p/2})]) = ∑ eigenvalues(A†A)ᵢ^{p/2}.
   Use schattenNorm_trace_as_eigenvalue_sum.

3. ∑ eigenvalues(A†A)ᵢ^{p/2} = ∑ singularValues A i ^ p.
   Since singularValues A i = √(eigenvalues(A†A)ᵢ) (both now using isHermitian_mul_conjTranspose_self A.conjTranspose), we get singularValues A i ^ p = (√λᵢ)^p = λᵢ^{p/2} by sqrt_rpow_eq_rpow_half (with λᵢ ≥ 0 from Matrix.eigenvalues_conjTranspose_mul_self_nonneg).

For step 1: unfold schattenNorm, then ← Real.rpow_mul on nonneg base. The base is nonneg because it equals ∑ λᵢ^{p/2} with nonneg eigenvalues. Use schattenNorm_trace_as_eigenvalue_sum to rewrite to the sum, then the sum is nonneg by Finset.sum_nonneg + Real.rpow_nonneg.

For step 3: use Finset.sum_congr and sqrt_rpow_eq_rpow_half with nonneg eigenvalue.
-/
lemma schattenNorm_rpow_eq_sum_singularValues (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ^ p = ∑ i : d, singularValues A i ^ p := by
  unfold schattenNorm;
  rw [ ← Real.rpow_mul ( _ ), one_div_mul_cancel hp.ne', Real.rpow_one ];
  · convert schattenNorm_trace_as_eigenvalue_sum A p using 1
    generalize_proofs at *;
    refine' Finset.sum_congr rfl fun i _ => _;
    unfold singularValues; rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( _ ) ] ; ring_nf;
    simp +zetaDelta at *;
    exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i;
  · have h_nonneg : ∀ i : d, 0 ≤ ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i) ^ (p / 2) := by
      exact fun i => Real.rpow_nonneg ( by have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg A; aesop ) _;
    convert Finset.sum_nonneg fun i _ => h_nonneg i using 1;
    convert schattenNorm_trace_as_eigenvalue_sum A p using 1

/-
PROBLEM
The Schatten p-norm equals the ℓ^p quasi-norm of the singular values:
    `‖A‖_p = (∑ σᵢ(A)^p)^{1/p}`.

PROVIDED SOLUTION
This should follow from schattenNorm_rpow_eq_sum_singularValues. We have schattenNorm A p ^ p = ∑ σᵢ^p. Since the sum is nonneg (each σᵢ^p ≥ 0) and schattenNorm is nonneg, we can take p-th roots: schattenNorm A p = (∑ σᵢ^p)^{1/p}. Use Real.rpow_inv_eq or the fact that if x^p = y then x = y^{1/p} for nonneg x, y and p > 0.
-/
lemma schattenNorm_eq_sum_singularValues_rpow (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = (∑ i : d, singularValues A i ^ p) ^ (1/p) := by
  rw [ ←schattenNorm_rpow_eq_sum_singularValues A hp ];
  rw [ ← Real.rpow_mul ( by exact Real.rpow_nonneg ( by
    simp [ Matrix.trace ];
    refine' Finset.sum_nonneg fun i _ => _;
    rw [ Matrix.IsHermitian.cfc ];
    simp [ Matrix.mul_apply, Matrix.diagonal ];
    field_simp;
    exact Finset.sum_nonneg fun _ _ => mul_nonneg ( Real.rpow_nonneg ( by
      exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg A _ ) _ ) ( add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) ) _ ), mul_one_div_cancel hp.ne', Real.rpow_one ]

/-- `‖A‖_p^p` equals the same sum over sorted singular values. -/
lemma schattenNorm_rpow_eq_sum_sorted (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  rw [schattenNorm_rpow_eq_sum_singularValues A hp]
  exact sum_singularValues_rpow_eq_sum_sorted A p

open InnerProductSpace in
/--
Scalar trace Young inequality for PSD matrices:
⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q for PSD A, B and conjugate p, q > 1.
-/
lemma HermitianMat.trace_young
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace / p + (B ^ q).trace / q := by
  --TODO Cleanup
  have h_schatten : ∀ (i j : d), (A.H.eigenvalues i) * (B.H.eigenvalues j) ≤ (A.H.eigenvalues i)^p / p + (B.H.eigenvalues j)^q / q := by
    intro i j
    have h_young : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → (1 < p → 1 / p + 1 / q = 1 → a * b ≤ (a^p) / p + (b^q) / q) := by
      intro a b ha hb hp hpq
      have h_young : a * b ≤ (a^p) / p + (b^q) / q := by
        have h_conj : 1 / p + 1 / q = 1 := hpq
        have h_pos : 0 < p ∧ 0 < q := by
          use zero_lt_one.trans hp
          refine lt_of_not_ge fun h ↦ ?_
          rw [ div_eq_mul_inv, div_eq_mul_inv ] at h_conj
          nlinarith [inv_nonpos.2 h, inv_mul_cancel₀ (by linarith : p ≠ 0)]
        have := @Real.geom_mean_le_arith_mean
        specialize this { 0, 1 } ( fun i => if i = 0 then p⁻¹ else q⁻¹ ) ( fun i => if i = 0 then a ^ p else b ^ q ) ; simp_all [ ne_of_gt ];
        simpa only [ div_eq_inv_mul ] using this h_pos.1.le h_pos.2.le ( Real.rpow_nonneg ha _ ) ( Real.rpow_nonneg hb _ )
      exact h_young
    refine h_young _ _ ?_ ?_ hp hpq
    · exact (zero_le_iff.mp hA).eigenvalues_nonneg _
    · exact (zero_le_iff.mp hB).eigenvalues_nonneg _
  convert Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ( h_schatten i j ) ( show 0 ≤ ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2 by positivity ) using 1;
  convert HermitianMat.inner_eq_doubly_stochastic_sum A B using 1;
  simp [ Finset.sum_add_distrib, add_mul, Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm, HermitianMat.trace_rpow_eq_sum ];
  simp [ ← Finset.mul_sum, ← Finset.sum_comm, ];
  congr! 2;
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := Matrix.unitary_row_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i;
    · rw [ this, mul_one ];
    · simp [ Matrix.mul_assoc ];
      simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  · refine' Finset.sum_congr rfl fun i _ => _;
    have := Matrix.unitary_col_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i <;> simp_all [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
    simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

/-- For PSD `A` and Hermitian `B`, the product
`C = A^{1/2} * B` satisfies `C^* C = (A.conj B.mat).mat = B * A * B`. -/
lemma conjTranspose_half_mul_eq_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) :
    ((A ^ (1/2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1/2 : ℝ)).mat * B.mat)
    = (A.conj B.mat).mat := by
  have := HermitianMat.pow_half_mul hA; simp_all [ ← mul_assoc ] ;
  simp only [mul_assoc, this]

lemma schattenNorm_half_mul_rpow_eq_trace_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A)
    {α : ℝ} (hα : 0 < α) :
    (schattenNorm ((A ^ (1/2 : ℝ)).mat * B.mat) (2 * α)) ^ (2 * α) =
    ((A.conj B.mat) ^ α).trace := by
  have h_conj : ((A ^ (1 / 2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1 / 2 : ℝ)).mat * B.mat) = (A.conj B.mat).mat := by
    exact conjTranspose_half_mul_eq_conj hA;
  unfold schattenNorm;
  rw [ ← Real.rpow_mul ] <;> norm_num [ hα.ne' ];
  · ring_nf; norm_num [ hα.ne' ];
    rw [ ← Matrix.IsHermitian.cfc_eq ];
    rw [ Matrix.conjTranspose_conjTranspose ];
    exact congrArg Complex.re (congrArg Matrix.trace (congrArg (cfc fun x => x ^ α) h_conj));
  · have h_eigenvalues_nonneg : ∀ i, 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self ((A ^ (1 / 2 : ℝ)).mat * B.mat).conjTranspose).eigenvalues i := by
      intro i; exact (by
      have := Matrix.eigenvalues_conjTranspose_mul_self_nonneg ( ( A ^ ( 1 / 2 : ℝ ) ).mat * B.mat ) i; aesop;);
    simp_all [ Matrix.trace, Matrix.IsHermitian.cfc ];
    simp_all [ Matrix.mul_apply, Matrix.diagonal ];
    refine' Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => _;
    field_simp;
    exact mul_nonneg ( Real.rpow_nonneg ( h_eigenvalues_nonneg j ) _ ) (by positivity)

/-!
## Schatten–Hölder inequality

The *Schatten–Hölder inequality* for matrix products:
For matrices `A`, `B` and exponents `r, p, q > 0` with `1/r = 1/p + 1/q`,
the Schatten `r`-norm of the product satisfies
  `‖A * B‖_{S^r} ≤ ‖A‖_{S^p} * ‖B‖_{S^q}`.
This version includes the quasi-norm case (r, p, q < 1).

### Proof sketch

The proof proceeds in three steps:
1. Express Schatten norms in terms of singular values:
   `‖A‖_p = (∑ σᵢ(A)^p)^{1/p}`.
2. Use the **weak log-majorization** of singular values of products
   (`weakLogMaj_singularValues_mul` + `sum_rpow_le_of_weakLogMaj`) to obtain
   `∑ σᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.
3. Apply the **classical Hölder inequality** for finite sums
   (`NNReal.inner_le_Lp_mul_Lq` from Mathlib, with conjugate exponents
   `p/r` and `q/r`) to bound
   `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σᵢ(A)^p)^{r/p} · (∑ σᵢ(B)^q)^{r/q}`.
4. Take `1/r`-th powers and combine.
-/
lemma schattenNorm_mul_le (A B : Matrix d d ℂ) {r p q : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hpqr : 1 / r = 1 / p + 1 / q) :
    schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B q := by
  -- It suffices to show the inequality for r-th powers, since x ↦ x^{1/r} is monotone.
  rw [schattenNorm_eq_sum_singularValues_rpow (A * B) hr,
      schattenNorm_eq_sum_singularValues_rpow A hp,
      schattenNorm_eq_sum_singularValues_rpow B hq]
  -- Rewrite sums over d to sums over Fin (Fintype.card d) via sorted singular values
  rw [sum_singularValues_rpow_eq_sum_sorted (A * B) r,
      sum_singularValues_rpow_eq_sum_sorted A p,
      sum_singularValues_rpow_eq_sum_sorted B q]
  -- Now we need:
  -- (∑ σ↓ᵢ(AB)^r)^{1/r} ≤ (∑ σ↓ᵢ(A)^p)^{1/p} · (∑ σ↓ᵢ(B)^q)^{1/q}
  -- Step 1: From sum_rpow_singularValues_mul_le, we have
  --   ∑ σ↓ᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r
  have h_sv_ineq := sum_rpow_singularValues_mul_le A B hr
  -- Step 2: From holder_step_for_singularValues, we have
  --   ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}
  have h_holder := holder_step_for_singularValues A B hr hp hq hpqr
  -- Step 3: Combine and take 1/r-th power
  -- Need: (∑ σ↓ᵢ(AB)^r)^{1/r} ≤ ((∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q})^{1/r}
  --      = (∑ σ↓ᵢ(A)^p)^{1/p} · (∑ σ↓ᵢ(B)^q)^{1/q}
  have h_combined : ∑ i, singularValuesSorted (A * B) i ^ r ≤
      (∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
      (∑ i, singularValuesSorted B i ^ q) ^ (r / q) :=
    le_trans h_sv_ineq h_holder
  -- Take 1/r-th power of both sides
  have h_rpow : (∑ i, singularValuesSorted (A * B) i ^ r) ^ (1/r) ≤
      ((∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
       (∑ i, singularValuesSorted B i ^ q) ^ (r / q)) ^ (1/r) := by
    apply Real.rpow_le_rpow
    · exact Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    · exact h_combined
    · positivity
  -- Simplify the RHS: (X^{r/p} · Y^{r/q})^{1/r} = X^{1/p} · Y^{1/q}
  have h_simplify :
      ((∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
       (∑ i, singularValuesSorted B i ^ q) ^ (r / q)) ^ (1/r) =
      (∑ i, singularValuesSorted A i ^ p) ^ (1/p) *
      (∑ i, singularValuesSorted B i ^ q) ^ (1/q) := by
    have hsp : 0 ≤ (∑ i, singularValuesSorted A i ^ p) ^ (r / p) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _) _
    have hsq : 0 ≤ (∑ i, singularValuesSorted B i ^ q) ^ (r / q) :=
      Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _) _
    rw [Real.mul_rpow hsp hsq]
    have hsp' : (0 : ℝ) ≤ ∑ i, singularValuesSorted A i ^ p :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    have hsq' : (0 : ℝ) ≤ ∑ i, singularValuesSorted B i ^ q :=
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg _ _) _
    congr 1 <;> rw [← Real.rpow_mul (by assumption)] <;> congr 1 <;> field_simp
  linarith

lemma HermitianMat.trace_rpow_conj_le
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / (2 * α) = 1 / p + 1 / q) :
    ((A.conj B.mat) ^ α).trace ≤
    (((A ^ (p / 2)).trace) ^ (1 / p) * ((B ^ q).trace) ^ (1 / q)) ^ (2 * α) := by
  -- Raise both sides of the inequality to the power of $2\alpha$.
  have h_exp : ((A.conj B.mat) ^ α).trace ≤ (schattenNorm (A ^ (1 / 2 : ℝ)).mat p * schattenNorm B.mat q) ^ (2 * α) := by
    have h_exp : (schattenNorm ((A ^ (1 / 2 : ℝ)).mat * B.mat) (2 * α)) ^ (2 * α) = ((A.conj B.mat) ^ α).trace := by
      exact schattenNorm_half_mul_rpow_eq_trace_conj hA hα
    rw [← h_exp]
    -- Apply the Schatten-Hölder inequality to the matrices $A^{1/2} * B$.
    refine Real.rpow_le_rpow ?_ (schattenNorm_mul_le _ _ (by positivity) hp hq hpq) (by positivity)
    exact schattenNorm_nonneg _ _
  rw [schattenNorm_hermitian_pow (rpow_nonneg hA) hp, schattenNorm_hermitian_pow hB hq] at h_exp
  have h_exp_simp : (A ^ (1 / 2 : ℝ)) ^ p = A ^ (p / 2 : ℝ) := by
    rw [← HermitianMat.rpow_mul hA]
    ring_nf
  rw [h_exp_simp] at h_exp
  exact h_exp