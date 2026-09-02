/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma raw_uphase_eq_is_1 {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  {u : Matrix T U ℂ} (ne0_u : u ≠ 0)
  {z : ℂ}
  (eq : z • u = u) :
  z = 1

- lemma raw_phase_star_move (a b c : ℂ)
  (norm_b : ‖b‖ = 1) :
  a * star b = c ↔ a = b * c

- lemma raw_uphase_div {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  (z z' : ℂ) (u u' : Matrix T U ℂ)
  (norm_z' : ‖z'‖ = 1)
  (eq : z • u = z' • u') :
  let r
-/

import Mathlib


lemma raw_uphase_eq_is_1 {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  {u : Matrix T U ℂ} (ne0_u : u ≠ 0)
  {z : ℂ}
  (eq : z • u = u) :
  z = 1 := by
    -- Since $u$ is not the zero matrix, there exists some entry $u_{ij} \neq 0$.
    obtain ⟨i, j, hij⟩ : ∃ i j, u i j ≠ 0 := by
      -- Since $u$ is not the zero matrix, there must be at least one entry $u_{ij} \neq 0$.
      by_contra h_contra; push_neg at h_contra; exact ne0_u (by ext i j; exact h_contra i j);
    -- Since $u$ is not the zero matrix, there exists some entry $u_{ij} \neq 0$. From the equation $z \cdot u_{ij} = u_{ij}$, we can divide both sides by $u_{ij}$ (since $u_{ij} \neq 0$) to get $z = 1$.
    have hz_eq_one : z * u i j = u i j := by
      -- Since $z • u = u$, we have $z * u i j = u i j$ for all $i$ and $j$.
      apply congr_fun (congr_fun eq i) j;
    -- Since $u_{ij} \neq 0$, we can divide both sides of the equation $z * u_{ij} = u_{ij}$ by $u_{ij}$ to get $z = 1$.
    field_simp [hij] at hz_eq_one ⊢
    exact hz_eq_one

-- slightly broken, human fix needed
lemma raw_phase_star_move (a b c : ℂ)
  (norm_b : ‖b‖ = 1) :
  a * star b = c ↔ a = b * c := by
    -- Since $b$ has norm 1, we have $star b = 1/b$.
    have h_star_b : star b = 1 / b := by
      -- Since $b$ has norm 1, we have $|b|^2 = b \cdot \overline{b} = 1$.
      have h_norm : b * star b = 1 := by
        -- Since $b$ is a complex number with norm 1, we have $b * \overline{b} = 1$ by definition of the norm.
        simp [Complex.mul_conj];
        -- Since ‖b‖ = 1, we have Complex.normSq b = 1 by definition of the norm.
        simp [Complex.normSq_eq_norm_sq, norm_b];
      exact eq_one_div_of_mul_eq_one_right h_norm;
    by_cases hb : b = 0 <;> simp_all +decide;
    -- Since $b \neq 0$, we can multiply both sides of the equation $a * b⁻¹ = c$ by $b$ to get $a = b * c$.
    field_simp [hb]
    -- Since multiplication is commutative in the complex numbers, we have $c * b = b * c$.
--    rw [mul_comm]

#check SemigroupAction.mul_smul

lemma raw_uphase_div {T U}
  [Nonempty T] [Nonempty U] [Fintype T] [Fintype U]
  (z z' : ℂ) (u u' : Matrix T U ℂ)
  (norm_z' : ‖z'‖ = 1)
  (eq : z • u = z' • u') :
  let r := z * star z'
  r • u = u' := by
    convert congr_arg ( fun x => star z' • x ) eq using 1;
    · -- By the associativity of scalar multiplication, we have $(z * star z') • u = star z' • (z • u)$.
      simp [mul_comm, smul_smul];
    · simp +decide [ ← SemigroupAction.mul_smul ];
      -- Since $z'$ has norm 1, we have $z' * \overline{z'} = 1$.
      have h_norm : z' * starRingEnd ℂ z' = 1 := by
        simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_z' ];
      rw [ mul_comm, h_norm, one_smul ]
