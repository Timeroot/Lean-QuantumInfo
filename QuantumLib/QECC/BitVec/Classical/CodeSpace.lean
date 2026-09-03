/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Runzhou Tao
-/

import QuantumLib.QECC.BitVec.States.BitVec
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel

/-!
# Classical linear codes

A `CodeSpace n` is a linear subspace of `(Fin n → ZMod 2)`.  This file records the standard
notions: generator and parity check matrices, the dual code, and the code distance, together
with the dimension count `dim C + dim C^⊥ = n` and the involutivity of duality.
-/

abbrev CodeSpace (n : ℕ) := Submodule (ZMod 2) (Fin n → ZMod 2)

variable {n : ℕ}

def codeFromGenerators (G : Finset (Fin n → ZMod 2)) : CodeSpace n :=
  Submodule.span (ZMod 2) G

/-- The code spanned by the rows of `M`. -/
def Matrix.toCodeSpace {α : Type*} (M : Matrix α (Fin n) (ZMod 2)) : CodeSpace n :=
  M.rowSpace

def CodeSpace.dualCode (C : CodeSpace n) : CodeSpace n := C.orthogonalBilin (dotProductBilin _ _)

noncomputable section

def CodeSpace.toFinset (C : CodeSpace n) : Finset (Fin n → ZMod 2) :=
  (C : Set (Fin n → ZMod 2)).toFinset

def CodeSpace.nonzero (C : CodeSpace n) : Finset (Fin n → ZMod 2) :=
  C.toFinset.filter (fun v => v != 0)

def CodeSpace.selfDual (C : CodeSpace n) : Prop := C.toFinset ⊆ C.dualCode.toFinset

def CodeSpace.nontrivial (C : CodeSpace n) : Prop := Finset.Nonempty C.nonzero

/-- The minimum Hamming weight of a nonzero codeword. -/
def CodeSpace.distance (C : CodeSpace n) (nt : C.nontrivial) : ℕ :=
  Finset.min' (C.nonzero.image hammingNorm) (Finset.image_nonempty.2 nt)

variable {α : Type*}

/-- `G` spans `C`; weaker than being a generator matrix, as the rows need not be independent. -/
def CodeSpace.spanned_by (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2)) : Prop :=
  G.rowSpace = C

def CodeSpace.generatorMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2)) : Prop :=
  LinearIndependent (ZMod 2) G.row ∧ C.spanned_by G

lemma CodeSpace.generatorMatrixOf_toCodeSpace {G : Matrix α (Fin n) (ZMod 2)}
    (hG : LinearIndependent (ZMod 2) G.row) : G.toCodeSpace.generatorMatrixOf G :=
  ⟨hG, rfl⟩

lemma CodeSpace.toCodeSpace_spanned_by {G : Matrix α (Fin n) (ZMod 2)} :
    G.toCodeSpace.spanned_by G :=
  rfl

def CodeSpace.parityCheckMatrixOf (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2)) : Prop :=
  C.dualCode.generatorMatrixOf G

/-- A parity check matrix whose rows need not be independent. -/
def CodeSpace.parity_checked_by (C : CodeSpace n) (G : Matrix α (Fin n) (ZMod 2)) : Prop :=
  C.dualCode.spanned_by G

lemma CodeSpace.spanned_by.row_mem {C : CodeSpace n} {G : Matrix α (Fin n) (ZMod 2)}
    (hsp : C.spanned_by G) (x : α) : G x ∈ C := by
  rw [← hsp]
  exact Submodule.subset_span (Set.mem_range_self (f := G.row) x)

lemma CodeSpace.pc_prod_mem_dual (C : CodeSpace n) {H : Matrix α (Fin n) (ZMod 2)} (x : α)
    (hpc : C.parityCheckMatrixOf H) : H x ∈ C.dualCode :=
  hpc.2.row_mem x

lemma CodeSpace.pcb_prod_mem_dual (C : CodeSpace n) {H : Matrix α (Fin n) (ZMod 2)} (x : α)
    (hpc : C.parity_checked_by H) : H x ∈ C.dualCode :=
  hpc.row_mem x

lemma CodeSpace.gm_prod_mem (C : CodeSpace n) {G : Matrix α (Fin n) (ZMod 2)} (x : α)
    (hgm : C.generatorMatrixOf G) : G x ∈ C :=
  hgm.2.row_mem x

theorem generatorMatrix_image_eq_CodeSpace [Fintype α] (C : CodeSpace n)
    (G : Matrix α (Fin n) (ZMod 2)) (hgen : C.generatorMatrixOf G) (x : Fin n → ZMod 2) :
    x ∈ C ↔ ∃ v, G.transpose.mulVec v = x := by
  rw [← hgen.2, Matrix.rowSpace, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun v => Eq.congr_left (funext fun j => ?_)
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem genMatrix_size_eq {k : ℕ} (C : CodeSpace n) (G : Matrix (Fin k) (Fin n) (ZMod 2))
    (hgen : C.generatorMatrixOf G) : Module.finrank (ZMod 2) C = k := by
  rw [← hgen.2, Matrix.rowSpace, finrank_span_eq_card hgen.1, Fintype.card_fin]

lemma dual_finrank_eq {C : CodeSpace n} :
    Module.finrank (ZMod 2) C.dualCode = n - Module.finrank (ZMod 2) C := by
  let B : LinearMap.BilinForm (ZMod 2) (Fin n → ZMod 2) :=
    Matrix.toBilin' (1 : Matrix (Fin n) (Fin n) (ZMod 2))
  have hdual : C.dualCode = B.orthogonal C := by
    ext x
    constructor
    · intro hx n₁ hn₁
      simpa [B, Matrix.toBilin'_apply', dotProductBilin] using hx n₁ hn₁
    · intro hx n₁ hn₁
      simpa [B, Matrix.toBilin'_apply', dotProductBilin] using hx n₁ hn₁
  have hB_nondeg : B.Nondegenerate := by
    simpa [B] using
      (Matrix.Nondegenerate.of_det_ne_zero
        (M := (1 : Matrix (Fin n) (Fin n) (ZMod 2)))
        (by simp)).toBilin'
  rw [hdual]
  simpa [Module.finrank_fin_fun] using LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nondeg C

theorem dual_dual_eq {C : CodeSpace n} : C.dualCode.dualCode = C := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.le_orthogonalBilin_orthogonalBilin
    intro a b
    simp only [dotProductBilin_apply_apply, dotProduct_comm]
    exact fun x => x
  rw [dual_finrank_eq, dual_finrank_eq]
  have h_rank : Module.finrank (ZMod 2) C ≤ n :=
    le_of_le_of_eq (Submodule.finrank_le _) (Module.finrank_fin_fun _)
  exact (Nat.sub_sub_self h_rank).symm

theorem pc_size_eq {k : ℕ} (C : CodeSpace n) (H : Matrix (Fin k) (Fin n) (ZMod 2))
    (hpc : C.parityCheckMatrixOf H) : k = n - Module.finrank (ZMod 2) C := by
  rw [← genMatrix_size_eq C.dualCode H hpc]
  exact dual_finrank_eq
