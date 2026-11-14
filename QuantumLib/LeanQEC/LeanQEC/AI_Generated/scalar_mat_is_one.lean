/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma scalar_mat_is_one {T T'} [Fintype T] [Fintype T'] [Nonempty T] [Nonempty T']
  {M : Matrix T T' ℂ} {s : ℂ} (ne0_M: M ≠ 0) (eq: s • M = M) :
  s = 1
-/

import Mathlib


lemma scalar_mat_is_one {T T'} [Fintype T] [Fintype T'] [Nonempty T] [Nonempty T']
  {M : Matrix T T' ℂ} {s : ℂ} (ne0_M: M ≠ 0) (eq: s • M = M) :
  s = 1 := by
    -- Since $M \neq 0$, there exists some $i$ and $j$ such that $M_{ij} \neq 0$.
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      -- Since $M \neq 0$, there must exist some $i$ and $j$ such that $M i j \neq 0$.
      by_contra h_contra; push_neg at h_contra; exact ne0_M (by ext i j; exact h_contra i j);
    -- Since $M_{ij} \neq 0$, we can divide both sides of $s * M_{ij} = M_{ij}$ by $M_{ij}$ to get $s = 1$.
    have hs : s * M i j = M i j := by
      -- By taking the (i, j) entry of both sides of the equation s • M = M, we get s * M i j = M i j.
      apply congr_fun (congr_fun eq i) j;
    exact mul_left_cancel₀ hij <| by simpa [ hij ] using hs;