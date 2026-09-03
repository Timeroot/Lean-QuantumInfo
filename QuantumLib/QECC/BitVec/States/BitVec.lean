/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm
-/

import Mathlib.Data.BitVec
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Indexing states by bitvectors

`BitVec n` is used throughout as the index type for an `n`-qubit register.  This file sets up the
`Fintype` instance, the concatenation equivalence `bits_cat : BitVec w₁ × BitVec w₂ ≃ BitVec
(w₁ + w₂)`, and the induced tensor product `ket_prod` of vectors.
-/

open Matrix

instance fin_bits (m : ℕ) : Fintype (BitVec m) :=
  Fintype.ofEquiv (Fin (2 ^ m)) ((BitVec.equivFin (m := m)).symm)

lemma Fintype.card_bitvec (m : ℕ) : Fintype.card (BitVec m) = 2 ^ m :=
  (Fintype.card_congr (BitVec.equivFin (m := m)).toEquiv).trans (Fintype.card_fin _)

def bits_cat {w₁ w₂} : BitVec w₁ × BitVec w₂ ≃ BitVec (w₁ + w₂) where
  toFun := fun (s1, s2) => BitVec.cast (by rw [Nat.add_comm]) (s2 ++ s1)
  invFun := fun s => (BitVec.extractLsb' 0 w₁ s,
    BitVec.extractLsb' w₁ w₂ s)
  left_inv := by
    intro s
    cases s with | _ s1 s2 =>
    apply Prod.ext
    · ext i ltw1_i
      simp
      have H: (s2 ++ s1).getLsbD i = (s2 ++ s1)[i] := rfl
      rw [H, BitVec.getElem_append]
      simp [ltw1_i]
    · ext i ltw2_i
      simp
      have H: (s2 ++ s1).getLsbD (w₁ + i) = (s2 ++ s1)[w₁ + i] := rfl
      rw [H, BitVec.getElem_append]
      have hfalse : ¬ w₁ + i < w₁ :=
        Nat.not_lt.mpr (Nat.le_add_right _ _)
      simp [hfalse]
  right_inv := by
    intro s
    ext i rg_i
    simp
    rw [BitVec.getElem_append]
    by_cases H : i < w₁
    · simp [H]
      rfl
    · simp [H]
      rw [<- Nat.add_sub_assoc]
      · simp
        rfl
      · exact not_lt.mp H

abbrev normalize_mat {n₁ m₁ n₂ m₂} :
  Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ ≃
  Matrix (BitVec (n₁ + m₁)) (BitVec (n₂ + m₂)) ℂ :=
  Matrix.reindex bits_cat bits_cat

def normalized_kron {n₁ m₁ n₂ m₂}
  (U₁ : Matrix (BitVec m₁) (BitVec n₁) ℂ)
  (U₂ : Matrix (BitVec m₂) (BitVec n₂) ℂ) :=
  normalize_mat (Matrix.kronecker U₁ U₂)

lemma normalize_mat_mul {n₁ m₁ n₂ m₂ n₃ m₃}
  (U : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ)
  (U' : Matrix (BitVec n₂ × BitVec m₂) (BitVec n₃ × BitVec m₃) ℂ) :
  normalize_mat (U * U') =
  normalize_mat U * normalize_mat U' := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
  apply Matrix.submatrix_mul
  exact bits_cat.symm.bijective

def toMat {t} : (t → ℂ) ≃ (Matrix t (BitVec 0) ℂ) where
  toFun := fun (v n _) => v n
  invFun := fun (m i) => m i 0
  left_inv := by
    intro m
    funext i
    rfl
  right_inv := by
    intro m
    apply Matrix.ext
    intro i j
    simp
    have H : j = 0#0 := by
      apply Subsingleton.elim
    rewrite [H]
    rfl

@[simp]
lemma toMat_apply {t} (v : t → ℂ) (i : t) (j : BitVec 0) : toMat v i j = v i :=
  rfl

@[simp]
lemma toMat_symm_apply {t} (M : Matrix t (BitVec 0) ℂ) (i : t) : toMat.symm M i = M i 0 :=
  rfl

lemma mulvec_toMat {t u} {fin_u : Fintype u} (U : Matrix t u ℂ) (v : u → ℂ) :
  toMat (U *ᵥ v) = U * (toMat v) := by
    ext n j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

def ket_prod {n₁ n₂}
    (v1 : BitVec n₁ → ℂ)
    (v2 : BitVec n₂ → ℂ) :=
  toMat.symm (normalized_kron (toMat v1) (toMat v2))

@[simp]
lemma ket_prod_apply {n m} (v : BitVec n → ℂ) (w : BitVec m → ℂ) (x : BitVec (n + m)) :
  ket_prod v w x = v (bits_cat.symm x).1 * w (bits_cat.symm x).2 :=
  rfl

lemma ket_prod_linear_left {n m} (v1 v2 : BitVec n → ℂ) (w : BitVec m → ℂ) (a b : ℂ) :
  ket_prod (a • v1 + b • v2) w = a • ket_prod v1 w + b • ket_prod v2 w := by
    ext x
    simp
    ring

lemma ket_prod_linear_right {n m} (v1 v2 : BitVec n → ℂ) (w : BitVec m → ℂ) (a b : ℂ) :
  ket_prod w (a • v1 + b • v2) = a • ket_prod w v1 + b • ket_prod w v2 := by
    ext x
    simp
    ring

lemma kron_prod {n₁ m₁ n₂ m₂}
    (U₁ : Matrix (BitVec m₁) (BitVec n₁) ℂ)
    (U₂ : Matrix (BitVec m₂) (BitVec n₂) ℂ)
    (v₁ : BitVec n₁ → ℂ)
    (v₂ : BitVec n₂ → ℂ) :
  ket_prod (U₁ *ᵥ v₁) (U₂ *ᵥ v₂) =
  (normalized_kron U₁ U₂) *ᵥ (ket_prod v₁ v₂) := by
  rw [ket_prod, mulvec_toMat, mulvec_toMat]
  rw [normalized_kron, kronecker, Matrix.mul_kronecker_mul]
  have H : kroneckerMap (fun x1 x2 ↦ x1 * x2) U₁ U₂ = kronecker U₁ U₂ :=
    by rfl
  rw [H]
  have H' : kroneckerMap (fun x1 x2 ↦ x1 * x2) (toMat v₁) (toMat v₂) =
    kronecker (toMat v₁) (toMat v₂) := by rfl
  rw [H']
  rw [normalize_mat_mul]
  rw [toMat.symm_apply_eq, mulvec_toMat, ket_prod, toMat.apply_symm_apply]
  rfl

@[simp]
theorem BitVec.sum_univ_one {M : Type u_2} [AddCommMonoid M] (f : BitVec 1 → M) :
  ∑ i : BitVec 1, f i = f 0 + f 1 := by
  rw [Finset.sum]
  have: Finset.univ.val = {0#1, 1#1} := by rfl
  simp [this]

def beq : Fin 2 ≃ BitVec 1 := (@BitVec.equivFin 1).symm

lemma BitVec1_cases (i : BitVec 1) : i = 0#1 ∨ i = 1#1 := by
  rcases i with ⟨ _ | _ | i, hi ⟩ <;> tauto

lemma normalize_mat_ext {n₁ n₂ m₁ m₂}
  (M : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ)
  (M' : Matrix (BitVec n₁ × BitVec m₁) (BitVec n₂ × BitVec m₂) ℂ) :
  normalize_mat M = normalize_mat M' →
  M = M' := by
    intro H
    apply (congrArg normalize_mat.symm) at H
    aesop
