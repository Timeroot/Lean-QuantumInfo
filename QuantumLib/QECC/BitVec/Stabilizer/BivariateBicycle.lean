/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Runzhou Tao, Yi Lee
-/

import QuantumLib.QECC.BitVec.Stabilizer.CSS
import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel

/-!
# Bivariate bicycle codes

The ingredients of the bivariate bicycle construction of Bravyi et al.: cyclic shift matrices on an
`l × m` torus, the two commuting generators `BB_x` and `BB_y`, sums of three or four monomials in
them, and horizontal stacking to form the `X` and `Z` parity checks.
-/

/-- The Kronecker product of two `Fin`-indexed matrices, reindexed back to a `Fin`-indexed one. -/
def Matrix.kronecker_fin {R : Type*} [Mul R] {m n p q : ℕ}
  (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R) :
  Matrix (Fin (m * p)) (Fin (n * q)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A.kronecker B)

/-- The permutation matrix cyclically shifting `Fin n` by `k`. -/
@[simp]
def cyclic_shift (n k : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if ((i + k) % n) = j then 1 else 0

/-- The generator `xᵏ` of the first cyclic factor of an `l × m` torus. -/
@[simp]
def BB_x (l m k : ℕ) [NeZero l] : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  Matrix.kronecker_fin (cyclic_shift l k) 1

/-- The generator `yᵏ` of the second cyclic factor of an `l × m` torus. -/
@[simp]
def BB_y (l m k : ℕ) [NeZero m] : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  Matrix.kronecker_fin 1 (cyclic_shift m k)

/-- A sum of three monomials in `x` and `y`; each `Mᵢ` is a flag choosing `x` or `y`,
together with the exponent. -/
@[simp]
def BB3_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)
 : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (BB_x l m M₁.2) else (BB_y l m M₁.2)
  let N₂ := if M₂.1 then (BB_x l m M₂.2) else (BB_y l m M₂.2)
  let N₃ := if M₃.1 then (BB_x l m M₃.2) else (BB_y l m M₃.2)
  N₁ + N₂ + N₃

/-- A sum of four monomials in `x` and `y`. -/
@[simp]
def BB4_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ M₄ : Bool × ℕ)
 : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (BB_x l m M₁.2) else (BB_y l m M₁.2)
  let N₂ := if M₂.1 then (BB_x l m M₂.2) else (BB_y l m M₂.2)
  let N₃ := if M₃.1 then (BB_x l m M₃.2) else (BB_y l m M₃.2)
  let N₄ := if M₄.1 then (BB_x l m M₄.2) else (BB_y l m M₄.2)
  N₁ + N₂ + N₃ + N₄

/-- Place two matrices side by side. -/
def Matrix.hstack_fin {α γ : Type*} {c₁ c₂ : ℕ}
(M₁ : Matrix α (Fin c₁) γ) (M₂ : Matrix α (Fin c₂) γ)
 : Matrix α (Fin (c₁ + c₂)) γ :=
 fun i j =>
  j.addCases (M₁ i) (M₂ i)
