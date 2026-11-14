/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

The following was proved by Aristotle:

- lemma kron_injective_up_to_scalar {T₁ U₁ T₂ U₂}
  [Fintype T₁] [Fintype T₂]
  [Fintype U₁] [Fintype U₂]
  {M₁ M₁' : Matrix T₁ U₁ ℂ}
  {M₂ M₂' : Matrix T₂ U₂ ℂ}
  (eq_krons: M₁.kronecker M₂ = M₁'.kronecker M₂')
  (ne0_M1: M₁ ≠ 0) (ne0_M2: M₂ ≠ 0) :
  exists (z : ℂˣ), (M₁ = z • M₁' /\ M₂ = z⁻¹ • M₂')
-/

import Mathlib


lemma kron_injective_up_to_scalar {T₁ U₁ T₂ U₂}
  [Fintype T₁] [Fintype T₂]
  [Fintype U₁] [Fintype U₂]
  {M₁ M₁' : Matrix T₁ U₁ ℂ}
  {M₂ M₂' : Matrix T₂ U₂ ℂ}
  (eq_krons: M₁.kronecker M₂ = M₁'.kronecker M₂')
  (ne0_M1: M₁ ≠ 0) (ne0_M2: M₂ ≠ 0) :
  exists (z : ℂˣ), (M₁ = z • M₁' /\ M₂ = z⁻¹ • M₂') := by
    -- By the properties of the Kronecker product, if $M_1 \otimes M_2 = M_1' \otimes M_2'$, then $M_1 = a \cdot M_1'$ and $M_2 = b \cdot M_2'$ for some scalars $a$ and $b$ such that $a \cdot b = 1$.
    obtain ⟨a, ha⟩ : ∃ a : ℂ, M₁ = a • M₁' := by
      -- Since $M_2 \neq 0$, there exists some $i, j$ such that $M_2 i j \neq 0$.
      obtain ⟨i, j, hij⟩ : ∃ i j, M₂ i j ≠ 0 := by
        contrapose! ne0_M2; aesop;
      -- Since $M₂ i j \neq 0$, we can divide both sides of the equation $M₁ a b * M₂ i j = M₁' a b * M₂' i j$ by $M₂ i j$ to get $M₁ a b = (M₂' i j / M₂ i j) * M₁' a b$.
      have h_div : ∀ a b, M₁ a b = (M₂' i j / M₂ i j) * M₁' a b := by
        -- By the properties of the Kronecker product, we have $M₁ a b * M₂ i j = M₁' a b * M₂' i j$ for all $a, b, i, j$.
        have h_eq : ∀ a b i j, M₁ a b * M₂ i j = M₁' a b * M₂' i j := by
          exact fun a b i j => by simpa [ Matrix.kronecker_apply ] using congr_fun ( congr_fun eq_krons ( a, i ) ) ( b, j ) ;
        exact fun a b => by rw [ div_mul_eq_mul_div, eq_div_iff hij ] ; linear_combination' h_eq a b i j;
      exact ⟨ M₂' i j / M₂ i j, by ext a b; simpa using h_div a b ⟩;
    -- Let $b = a^{-1}$.
    use Units.mk0 a (by
    aesop)
    generalize_proofs at *;
    -- Since $a \neq 0$, we can divide both sides of $a • (M₁'.kronecker M₂) = M₁'.kronecker M₂'$ by $M₁'.kronecker M₂$ (which is non-zero because $M₂$ is non-zero).
    have h_div : a • M₂ = M₂' := by
      -- Substitute $M_1 = a \cdot M_1'$ into the equation $M_1 \otimes M_2 = M_1' \otimes M_2'$.
      have h_sub : (a • M₁').kronecker M₂ = M₁'.kronecker M₂' := by
        bound;
      -- Since $M_1'$ is non-zero, there exists some $i, j$ such that $(M_1')_{ij} \neq 0$.
      obtain ⟨i, j, hij⟩ : ∃ i j, (M₁') i j ≠ 0 := by
        contrapose! ne0_M1; aesop;
      ext k l; replace h_sub := congr_fun ( congr_fun h_sub ( i, k ) ) ( j, l ) ; aesop;
      grind;
    aesop;
    simp +decide [ pf, Units.smul_def ]
