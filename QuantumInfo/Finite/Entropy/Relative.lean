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

/-- The trace of cfc(f, A) equals the sum of f applied to eigenvalues. -/
lemma HermitianMat.trace_cfc_eq (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    (A.cfc f).trace = ∑ i, f (A.H.eigenvalues i) := by
  have h1 := HermitianMat.trace_eq_trace (A.cfc f)
  obtain ⟨e, he⟩ := HermitianMat.cfc_eigenvalues f A
  have h2 := (A.cfc f).H.trace_eq_sum_eigenvalues
  rw [he] at h2
  simp [Function.comp] at h2
  rw [HermitianMat.mat_cfc] at h1
  rw [h2] at h1
  have h3 : (Complex.ofReal) (A.cfc f).trace = Complex.ofReal (∑ i, f (A.H.eigenvalues (e i))) := by
    convert h1 using 1
    simp
  have h4 := Complex.ofReal_injective h3
  rw [h4]
  exact Equiv.sum_comp e (fun x => f (A.H.eigenvalues x))

/-- Tr[A^p] = ∑ᵢ λᵢ^p for a Hermitian matrix A. -/
lemma HermitianMat.trace_rpow_eq_sum (A : HermitianMat d ℂ) (p : ℝ) :
    (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p := by
  exact A.trace_cfc_eq (· ^ p)

/--
The inner product ⟪A, B⟫ equals ∑_{ij} a_i b_j w_{ij} where a_i, b_j are eigenvalues
and w_{ij} = ‖C_{ij}‖² for C = U_A^* U_B unitary.
-/
lemma HermitianMat.inner_eq_doubly_stochastic_sum
    (A B : HermitianMat d ℂ) :
    let C := A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val
    ⟪A, B⟫_ℝ = ∑ i, ∑ j,
      A.H.eigenvalues i * B.H.eigenvalues j * (‖C i j‖^2) := by
  -- By the properties of the trace and diagonalization, we can rewrite the trace of AB as the sum of the products of the eigenvalues of A and B, multiplied by the squared norms of the entries of the product of their eigenvector matrices.
  have h_trace_diag : Matrix.trace (A.mat * B.mat) = Matrix.trace ((A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * A.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ) * ((A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * B.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ))) := by
    have h_trace_diag : Matrix.trace (A.mat * B.mat) = Matrix.trace ((A.H.eigenvectorUnitary : Matrix d d ℂ) * ((A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * A.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ)) * ((A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * B.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ)) * (A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose) := by
      simp [ Matrix.mul_assoc ];
      simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
    rw [ h_trace_diag, Matrix.trace_mul_comm ];
    simp [ ← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  -- Since $A$ is Hermitian, its eigenvector matrix is unitary, and thus $(A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * A.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ)$ is diagonal with the eigenvalues of $A$ on the diagonal.
  have h_diag_A : (A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * A.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ) = Matrix.diagonal (fun i => A.H.eigenvalues i : d → ℂ) := by
    have := A.H.spectral_theorem;
    convert congr_arg ( fun x : Matrix d d ℂ => ( A.H.eigenvectorUnitary : Matrix d d ℂ ).conjTranspose * x * ( A.H.eigenvectorUnitary : Matrix d d ℂ ) ) this using 1 ; simp [ Matrix.mul_assoc ];
    simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  -- Since $B$ is Hermitian, its eigenvector matrix is unitary, and thus $(A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * B.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ)$ is diagonal with the eigenvalues of $B$ on the diagonal.
  have h_diag_B : (A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * B.mat * (A.H.eigenvectorUnitary : Matrix d d ℂ) = (A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * (B.H.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i => B.H.eigenvalues i : d → ℂ) * (B.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * (A.H.eigenvectorUnitary : Matrix d d ℂ) := by
    have h_diag_B : B.mat = (B.H.eigenvectorUnitary : Matrix d d ℂ) * Matrix.diagonal (fun i => B.H.eigenvalues i : d → ℂ) * (B.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose := by
      convert B.H.spectral_theorem using 1;
    grind;
  -- Since $C = U_A^* U_B$ is unitary, we have $C_{ij} = \langle u_i, v_j \rangle$ where $u_i$ and $v_j$ are the eigenvectors of $A$ and $B$, respectively.
  set C : Matrix d d ℂ := (A.H.eigenvectorUnitary : Matrix d d ℂ).conjTranspose * (B.H.eigenvectorUnitary : Matrix d d ℂ)
  have hC_unitary : C * C.conjTranspose = 1 := by
    simp +zetaDelta at *;
    simp [ Matrix.mul_assoc ];
    simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]
  have hC_norm : ∀ i j, ‖C i j‖ ^ 2 = (C i j) * (star (C i j)) := by
    simp [ Complex.mul_conj, Complex.normSq_eq_norm_sq ]
  have hC_trace : Matrix.trace (Matrix.diagonal (fun i => A.H.eigenvalues i : d → ℂ) * C * Matrix.diagonal (fun i => B.H.eigenvalues i : d → ℂ) * C.conjTranspose) = ∑ i, ∑ j, A.H.eigenvalues i * B.H.eigenvalues j * ‖C i j‖ ^ 2 := by
    simp [ Matrix.trace, Matrix.mul_apply, hC_norm ];
    simp [ Matrix.diagonal, Finset.sum_ite_eq ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring;
  convert congr_arg Complex.re hC_trace using 1;
  convert congr_arg Complex.re h_trace_diag using 1;
  rw [ h_diag_A, h_diag_B ] ; simp [ Matrix.mul_assoc ] ;
  simp +zetaDelta at *

/--
For a unitary matrix C, the row sums of ‖C i j‖^2 equal 1.
-/
lemma unitary_row_sum_norm_sq (C : Matrix d d ℂ) (hC : C * C.conjTranspose = 1) (i : d) :
    ∑ j, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC i i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Matrix.one_apply_eq] at hC
  exact_mod_cast hC

/--
For a unitary matrix C, the column sums of ‖C i j‖^2 equal 1.
-/
lemma unitary_col_sum_norm_sq (C : Matrix d d ℂ) (hC : C.conjTranspose * C = 1) (j : d) :
    ∑ i, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC j j)
  simp_rw [Matrix.mul_apply, mul_comm] at hC
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply_eq,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] at hC
  exact_mod_cast hC

/--
Scalar trace Young inequality for PSD matrices:
⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q for PSD A, B and conjugate p, q > 1.
-/
lemma HermitianMat.trace_young
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace / p + (B ^ q).trace / q := by
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
    have := unitary_row_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i;
    · rw [ this, mul_one ];
    · simp [ Matrix.mul_assoc ];
      simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  · refine' Finset.sum_congr rfl fun i _ => _;
    have := unitary_col_sum_norm_sq ( A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val ) ?_ i <;> simp_all [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
    simp [ ← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

--TODO: We don't actually use this, and it's not clear that it's useful (since it's just a
-- specialization); remove?
omit [DecidableEq d] in
/--
Weighted Jensen inequality: for weights w_j ≥ 0 with ∑ w_j = 1, values b_j ≥ 0,
and q ≥ 1: (∑_j w_j * b_j)^q ≤ ∑_j w_j * b_j^q.

This is the special case of `Real.rpow_arith_mean_le_arith_mean_rpow` applied to
`Finset.univ`
-/
lemma weighted_jensen_rpow (b w : d → ℝ) (q : ℝ)
  (hb : ∀ j, 0 ≤ b j) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (hq : 1 ≤ q) :
    (∑ j, w j * b j) ^ q ≤ ∑ j, w j * b j ^ q :=
  Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ _ _ (fun i _ ↦ hw i) hsum (fun i _ ↦ hb i) hq

omit [DecidableEq d] in
/--
Doubly stochastic Hölder inequality: for nonneg a, b, doubly stochastic w,
and conjugate p, q > 1:
∑_{ij} a_i * b_j * w_{ij} ≤ (∑ a_i^p)^{1/p} * (∑ b_j^q)^{1/q}.
-/
lemma doubly_stochastic_holder (a b : d → ℝ) (w : d → d → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ∑ i, ∑ j, a i * b j * w i j ≤ (∑ i, a i ^ p) ^ (1/p) * (∑ j, b j ^ q) ^ (1/q) := by
  by_contra h_contra
  contrapose! h_contra with h_contra
  simp_all [ ← Finset.mul_sum, mul_assoc ]
  have h0q : 0 < q :=
    lt_of_le_of_ne ( le_of_not_gt fun hq => by { rw [ inv_eq_one_div, div_eq_mul_inv ] at hpq; nlinarith [ inv_mul_cancel₀ ( by linarith : ( p : ℝ ) ≠ 0 ), inv_lt_zero.2 hq ] } ) (by grind)
  -- Apply Hölder's inequality with the sequences $a_i$ and $g_i = \sum_j w_{ij} b_j$.
  have h_holder : (∑ i, a i * (∑ j, w i j * b j)) ≤ (∑ i, a i ^ p) ^ (1 / p) * (∑ i, (∑ j, w i j * b j) ^ q) ^ (1 / q) := by
    have := @Real.inner_le_Lp_mul_Lq
    simp_all
    convert this Finset.univ a ( fun i => ∑ j, w i j * b j ) ( show p.HolderConjugate q from ?_ ) using 1
    · simp only [ha, abs_of_nonneg, mul_eq_mul_left_iff]
      left
      congr!
      symm
      exact abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (hw _ _) (hb _))
    · constructor <;> linarith
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ i, (∑ j, w i j * b j) ^ q ≤ ∑ j, b j ^ q := by
    -- Apply Jensen's inequality to the convex function $x^q$ with weights $w_{ij}$.
    have h_jensen : ∀ i, (∑ j, w i j * b j) ^ q ≤ ∑ j, w i j * b j ^ q := by
      intro i
      have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ q) := by
        apply convexOn_rpow
        nlinarith [ inv_pos.2 ( zero_lt_one.trans hp ), inv_pos.2 h0q, mul_inv_cancel₀ h0q.ne']
      convert h_jensen.map_sum_le _ _ _ <;> aesop
    refine' le_trans ( Finset.sum_le_sum fun i _ => h_jensen i ) _;
    rw [ Finset.sum_comm ]
    simp [ ← Finset.sum_mul, hcol]
  simp_all only [mul_comm];
  simpa using h_holder.trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Finset.sum_nonneg fun _ _ => mul_nonneg ( hb _ ) ( hw _ _ ) ) _ ) h_fubini (one_div_nonneg.mpr h0q.le)) ( Real.rpow_nonneg ( Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( ha _ ) _ ) _ ) ) |> le_trans <| by simp;

/--
Hermitian trace Hölder inequality: for PSD A, B and conjugate exponents p, q > 1,
⟪A, B⟫ ≤ Tr[A^p]^(1/p) * Tr[B^q]^(1/q).
-/
lemma HermitianMat.inner_le_trace_rpow_mul
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace ^ (1/p) * (B ^ q).trace ^ (1/q) := by
  by_cases hq : q > 1;
  · -- Apply the doubly_stochastic_holder lemma with the weights $w_{ij} = \|C_{ij}\|^2$.
    rw [trace_rpow_eq_sum, trace_rpow_eq_sum, inner_eq_doubly_stochastic_sum]
    refine doubly_stochastic_holder
      A.H.eigenvalues B.H.eigenvalues
      (fun i j ↦ ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2)
      (fun i ↦ by simpa using hA.eigenvalues_nonneg i)
      (fun i ↦ by simpa using hB.eigenvalues_nonneg i)
      (by bound) ?_ ?_ p q hp hpq
    · apply unitary_row_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
    · apply unitary_col_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
  · rcases eq_or_ne q 0 with _ | _
    · grind only [cases Or]
    · field_simp at hpq
      nlinarith

/-
PROBLEM
Trace subadditivity (Rotfeld's inequality): for PSD A, B and 0 < p ≤ 1,
Tr[(A + B)^p] ≤ Tr[A^p] + Tr[B^p].

PROVIDED SOLUTION
Use trace_rpow_eq_sum to express each side as sums of eigenvalues.
Then use the operator concavity of x^p on [0,∞) for 0 < p ≤ 1.

More specifically, use the CFC approach: since x ↦ x^p is concave on [0,∞),
by the Loewner-Heinz theorem / operator concavity:
  (A + B)^p ≤ A^p + B^p  (as operators)
for 0 < p ≤ 1 and A, B ≥ 0. This is exactly HermitianMat.cfc_concave_le
(if available) or can be proved from the operator concavity of t^p.

Taking traces preserves the ordering since trace is monotone on PSD matrices.
So Tr[(A+B)^p] ≤ Tr[A^p + B^p] = Tr[A^p] + Tr[B^p].

I DON'T THINK THIS IS ACTUALLY NEEDED.
-/
lemma HermitianMat.trace_rpow_add_le
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ((A + B) ^ p).trace ≤ (A ^ p).trace + (B ^ p).trace := by
  sorry

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

/-- If A ≥ 0 and A ≤ 1, then each eigenvalue of A is in [0, 1]. -/
lemma HermitianMat.eigenvalues_le_one_of_le_one
    (A : HermitianMat d ℂ) (hA1 : A ≤ 1) (i : d) :
    A.H.eigenvalues i ≤ 1 := by
  by_contra! h
  obtain ⟨v, hv₁, hv₂⟩ : ∃ v : EuclideanSpace ℂ d, ‖v‖ = 1 ∧ A.mat.mulVec v = (A.H.eigenvalues i) • v := by
    use A.H.eigenvectorBasis i
    exact ⟨A.H.eigenvectorBasis.orthonormal.1 i, A.H.mulVec_eigenvectorBasis i⟩
  have h_eigenvalue : star v ⬝ᵥ A.mat.mulVec v = (A.H.eigenvalues i) * star v ⬝ᵥ v := by
    rw [hv₂, dotProduct_smul, Complex.real_smul]
  have h_unit : star v ⬝ᵥ v = 1 := by
    simp only [EuclideanSpace.norm_eq, Real.sqrt_eq_one, dotProduct, Pi.star_apply,
      RCLike.star_def]  at hv₁ ⊢
    simp only [sq, Complex.ext_iff, Complex.re_sum, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, neg_mul, sub_neg_eq_add, Complex.im_sum,
      Complex.one_re, Complex.one_im] at hv₁ ⊢
    simp only [Complex.norm_def, Complex.normSq, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      mul_comm, add_neg_cancel, Finset.sum_const_zero, and_true] at hv₁ ⊢
    rw [← hv₁]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
  have := hA1.2 v
  simp only [val_eq_coe, mul_one, mat_one, Matrix.sub_mulVec,
    Matrix.one_mulVec, dotProduct_sub, h_eigenvalue, h_unit] at this
  norm_cast at this
  linarith

/-- For positive A ≤ 1 and p ≥ 1, `Tr[A^p] ≤ Tr[A]`.
-/
lemma HermitianMat.trace_rpow_le_trace_of_le_one
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    (A ^ p).trace ≤ A.trace := by
  -- Rewrite both sides using trace_rpow_eq_sum: Tr[A^p] = ∑ λ_i^p and Tr[A] = ∑ λ_i (using trace_rpow_eq_sum and rpow_one for the latter).
  have h_trace_eq_sum : (A ^ p).trace = ∑ i, (A.H.eigenvalues i) ^ p ∧ A.trace = ∑ i, (A.H.eigenvalues i) := by
    exact ⟨ by rw [ HermitianMat.trace_rpow_eq_sum ], by rw [ show A.trace = ∑ i, ( A.H.eigenvalues i ) by simpa using HermitianMat.trace_rpow_eq_sum A 1 ] ⟩;
  rw [ h_trace_eq_sum.1, h_trace_eq_sum.2 ];
  apply_rules [ Finset.sum_le_sum ];
  intro i hi; by_cases hi0 : A.H.eigenvalues i = 0 <;> simp_all
  · rw [ Real.zero_rpow ( by positivity ) ];
  · conv_rhs => rw [← (A.H.eigenvalues i).rpow_one]
    apply Real.rpow_le_rpow_of_exponent_ge
    · exact lt_of_le_of_ne' (le_of_not_gt fun hi => hi0 <| by linarith [ show 0 ≤ A.H.eigenvalues i by simpa using hA.eigenvalues_nonneg i ] ) hi0
    · exact A.eigenvalues_le_one_of_le_one hA1 i
    · exact hp

/-- Araki-Lieb-Thirring inequality for 0 < q ≤ 1: Tr[(B^r A B^r)^q] ≤ Tr[B^{rq} A^q B^{rq}]. -/
private lemma araki_lieb_thirring_le_one
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (r q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ((A.conj (B ^ r).mat) ^ q).trace ≤ ((A ^ q).conj (B ^ (r * q)).mat).trace := by
  sorry

/-
PROBLEM
Tr[(σ^t ρ σ^t)^α] ≤ 1 for 0 < α < 1, t = (1-α)/(2α).

PROVIDED SOLUTION
Step 1: By araki_lieb_thirring_le_one (ALT for q ≤ 1):
  Tr[(σ^t ρ σ^t)^α] ≤ Tr[σ^{tα} ρ^α σ^{tα}]
  = Tr[ρ^α σ^{2tα}] = Tr[ρ^α σ^{1-α}] = ⟪ρ^α, σ^{1-α}⟫.

  Apply araki_lieb_thirring_le_one with A = ρ.M, B = σ.M, r = t, q = α.
  LHS: ((ρ.M).conj (σ.M^t).mat)^α = exactly our term.
  RHS: (ρ.M^α).conj (σ.M^{t*α}).mat.
  The trace of the RHS = ⟪ρ^α, σ^{2tα}⟫ by inner_eq_trace and trace cyclicity.
  Since 2tα = (1-α), this is ⟪ρ^α, σ^{1-α}⟫.

Step 2: By inner_le_trace_rpow_mul with p = 1/α > 1, q' = 1/(1-α) > 1:
  ⟪ρ^α, σ^{1-α}⟫ ≤ Tr[(ρ^α)^{1/α}]^α * Tr[(σ^{1-α})^{1/(1-α)}]^{1-α}
  = Tr[ρ]^α * Tr[σ]^{1-α} = 1^α * 1^{1-α} = 1.

  Use rpow_mul to simplify (ρ^α)^{1/α} = ρ, etc.
  Use ρ.tr and σ.tr for Tr[ρ] = 1, Tr[σ] = 1.
-/
private theorem sandwiched_trace_of_lt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace ≤ 1 := by
  sorry

/-- For PSD A and p ≠ 0, `A^{-p} * A^p = HermitianMat.supportProj A`. -/
lemma HermitianMat.rpow_neg_mul_rpow_eq_supportProj
    {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    (A ^ (-p)).mat * (A ^ p).mat = A.supportProj.mat := by
  unfold HermitianMat.supportProj;
  have h_cfc : (A ^ (-p)).mat * (A ^ p).mat = (A.cfc (fun x => x ^ (-p))) * (A.cfc (fun x => x ^ p)) := by
    congr! 1;
  rw [ h_cfc, ← mat_cfc_mul ];
  have h_cfc : ∀ x : ℝ, 0 ≤ x → x ^ (-p) * x ^ p = if x = 0 then 0 else 1 := by
    intro x hx; by_cases hx' : x = 0 <;> simp [ hx', Real.rpow_neg, hx, hp ] ;
  have h_cfc_eq : (A.cfc (fun x => x ^ (-p) * x ^ p)) = (A.cfc (fun x => if x = 0 then 0 else 1)) := by
    apply cfc_congr_of_nonneg hA;
    exact fun x hx => h_cfc x hx;
  convert congr_arg ( fun x : HermitianMat d ℂ => x.val ) h_cfc_eq using 1;
  exact congr_arg ( fun x : HermitianMat d ℂ => x.val ) ( supportProj_eq_cfc A )

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
    exact supportProj_mul_self B
  have h_range_A_subset_range_B : LinearMap.range A.lin ≤ LinearMap.range B.lin := by
    have h_orthogonal_complement : LinearMap.range (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = (LinearMap.ker (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      have h_orthogonal_complement : ∀ (T : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d), T = T.adjoint → LinearMap.range T = (LinearMap.ker T)ᗮ := by
        intro T hT;
        refine' Submodule.eq_of_le_of_finrank_eq _ _;
        · rintro x ⟨y, rfl⟩
          rw [Submodule.mem_orthogonal' (LinearMap.ker T) (T y)]
          intro z hz
          rw [LinearMap.mem_ker] at hz
          simp [← LinearMap.adjoint_inner_right, ← hT, hz]
        · have := LinearMap.finrank_range_add_finrank_ker T;
          have := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker T)
          linarith;
      apply h_orthogonal_complement
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
    obtain ⟨w, hw⟩ : A.mat.mulVec v ∈ LinearMap.range B.lin := by
      exact h_range_A_subset_range_B ( Set.mem_range_self v );
    replace h_supportProj_mul_B := congr(Matrix.mulVec $h_supportProj_mul_B w)
    simpa only [← hw, ← Matrix.mulVec_mulVec] using h_supportProj_mul_B
  -- By definition of matrix multiplication, if B.supportProj * A * v = A * v for all vectors v, then B.supportProj * A = A.
  have h_matrix_eq : ∀ (M N : Matrix d d ℂ), (∀ v : EuclideanSpace ℂ d, M.mulVec (N.mulVec v) = N.mulVec v) → M * N = N := by
    intro M N hMN; ext i j; specialize hMN ( Pi.single j 1 ) ; replace hMN := congr_fun hMN i; aesop;
  rw [← Matrix.conjTranspose_inj]
  simp_all only [Matrix.mulVec_mulVec, Matrix.conjTranspose_mul, conjTranspose_mat, implies_true]

lemma HermitianMat.inner_supportProj_of_ker_le (A B : HermitianMat d ℂ)
  (h : LinearMap.ker B.lin ≤ LinearMap.ker A.lin) :
    ⟪A, B.supportProj⟫ = A.trace := by
  rw [inner_def, mul_supportProj_of_ker_le A B h, trace]

lemma supportProj_inner_density (h : σ.M.ker ≤ ρ.M.ker) :
    ⟪σ.M.supportProj, ρ.M⟫_ℝ = 1 := by
  rw [HermitianMat.inner_comm _ _, HermitianMat.inner_supportProj_of_ker_le ρ.M σ.M h,
    HermitianMat.trace_eq_re_trace]
  simp [MState.tr']

--PULLOUT
@[simp]
theorem HermitianMat.rpow_zero (A : HermitianMat d ℂ) : A ^ (0 : ℝ) = 1 := by
  simp [rpow_eq_cfc]

/-
⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 for density matrices ρ, σ with ker(σ) ≤ ker(ρ).
-/
private lemma sandwiched_inner_eq_one (h : σ.M.ker ≤ ρ.M.ker) (t : ℝ) :
    ⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have h_combine : (σ.M ^ (-2 * t)).mat * (σ.M ^ t).mat = (σ.M ^ (-t)).mat := by
      rw [show (-t : ℝ) = -2 * t + t by ring, HermitianMat.mat_rpow_add σ.nonneg]
      contrapose! ht
      linarith
    have h_support : (σ.M ^ t).mat * (σ.M ^ (-t)).mat = σ.M.supportProj.mat := by
      rw [← neg_ne_zero] at ht
      simpa only [neg_neg] using σ.M.rpow_neg_mul_rpow_eq_supportProj σ.nonneg ht
    rw [HermitianMat.inner_def, HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat]
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, h_combine]
    rw [Matrix.trace_mul_cycle, h_support, ← HermitianMat.inner_def]
    exact supportProj_inner_density h

private theorem sandwiched_trace_of_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    1 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  -- Let t = (1 - α) / (2 * α), A = ρ.M.conj (σ.M ^ t) and B = σ.M ^ (-2 * t)
  set t : ℝ := (1 - α) / (2 * α)
  set A := ρ.M.conj (σ.M ^ t).mat
  set B := σ.M ^ (-2 * t)
  have h_trace : ⟪A, B⟫ = 1 := sandwiched_inner_eq_one h t
  have h_inner : ⟪A, B⟫ ≤ (A ^ α).trace ^ (1 / α) * (B ^ (α / (α - 1))).trace ^ (1 / (α / (α - 1))) := by
    apply HermitianMat.inner_le_trace_rpow_mul
    · positivity
    · exact HermitianMat.rpow_nonneg σ.nonneg --TODO positivity
    · exact hα
    · rw [div_div_eq_mul_div, div_add_div, div_eq_iff]
      · ring
      · positivity
      · positivity
      · positivity
  have h_trace_B : (B ^ (α / (α - 1))).trace = 1 := by
    have hB : B ^ (α / (α - 1)) = σ.M ^ (-2 * t * (α / (α - 1))) := by
      rw [HermitianMat.rpow_mul σ.nonneg]
    have h : -2 * t * ( α / ( α - 1 ) ) = 1 := by
      rw [mul_div, div_eq_iff]
      · linarith [mul_div_cancel₀ (1 - α) (by linarith : (2 * α) ≠ 0)]
      · linarith only [hα]
    rw [hB, h]
    simp
  have h_final : 1 ≤ (A ^ α).trace ^ (1 / α) := by
    simpa only [h_trace, one_div, h_trace_B, Real.one_rpow, mul_one] using h_inner
  have : 0 ≤ (A ^ α).trace := by
    --TODO: Make this all discharge via just `positivity`.
    apply HermitianMat.trace_nonneg
    apply HermitianMat.rpow_nonneg
    positivity
  refine le_of_not_gt fun h => h_final.not_gt ?_
  simpa using Real.rpow_lt_one this h (by positivity)

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
