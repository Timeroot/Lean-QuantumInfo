/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Runzhou Tao, Mattias Ehatamm, Eashan Hatti
-/

import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel
import QuantumLib.QECC.Symplectic

/-!
# Check matrices in the binary symplectic representation

An `n`-qubit Pauli operator, read modulo phases, is a point of `QuantumLib.PauliOp.SympSpace n` —
an `X` part and a `Z` part over `ZMod 2` — and two of them commute exactly when `sympForm`
vanishes on the pair. A `BinSympMatrix k n` is `k` such points, read as the checks of a stabilizer
code: the errors it detects are the vectors not orthogonal to every row, so the undetectable ones
are those orthogonal to every row yet outside the row space. `BinSympMatrix.distance` is the least
weight of an undetectable error, falling back to `n + 1` when there is none.

`QECC.BitVec.Bridge.Symplectic` identifies all of this with `QuantumLib.PauliOp.StabGroup`: the row
space of a commuting check matrix is the symplectic image of a genuine stabilizer group, and the
distance here is that group's distance.
-/

open QuantumLib.PauliOp

namespace QuantumLib

variable {n : ℕ}

/-- Selecting the entries where an indicator vector is `1` is the same as multiplying by it. -/
lemma sum_univ_if_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    (ind : α → ZMod 2) (f : α → ZMod 2) :
    Finset.univ.sum (fun a => if ind a = 1 then f a else 0) =
      Finset.univ.sum (fun a => f a * ind a) := by
  exact Finset.sum_congr rfl fun x _ => by
    rcases Fin.exists_fin_two.mp ⟨ind x, rfl⟩ with h | h
    · have h01 : ¬ ((0 : ZMod 2) = 1) := by norm_num
      rw [h]
      change (if (0 : ZMod 2) = 1 then f x else 0) = f x * (0 : ZMod 2)
      simp [h01]
    · rw [h]
      change (if (1 : ZMod 2) = 1 then f x else 0) = f x * (1 : ZMod 2)
      simp

/-- `k` checks on `n` qubits in the binary symplectic representation: the `X` part and the `Z`
part of each check, as two `k × n` matrices over `ZMod 2`. -/
structure BinSympMatrix (k n : ℕ) where
  /-- The `X` part of each check. -/
  X : Matrix (Fin k) (Fin n) (ZMod 2)
  /-- The `Z` part of each check. -/
  Z : Matrix (Fin k) (Fin n) (ZMod 2)

/-- The `r`-th check, as a point of `SympSpace n`. -/
def BinSympMatrix.row {n k : ℕ} (bsm : BinSympMatrix k n) (r : Fin k) : SympSpace n :=
  (bsm.X r, bsm.Z r)

/-- The symplectic product of two checks, which vanishes exactly when they commute. -/
def BinSympMatrix.rowProd {n k : ℕ} (bsm : BinSympMatrix k n) (r₁ r₂ : Fin k) : (ZMod 2) :=
  sympForm n (bsm.row r₁) (bsm.row r₂)

/-- Every pair of checks commutes. -/
def BinSympMatrix.isCommuting {n k : ℕ} (bsm : BinSympMatrix k n) : Prop :=
  ∀ r₁ r₂, bsm.rowProd r₁ r₂ = 0

/-- The sum of the checks selected by an indicator vector is that vector multiplied into the two
check matrices. -/
lemma BinSympMatrix.selectedRows_sum_eq_mulVec {n k : ℕ} (bsm : BinSympMatrix k n)
    (ind : Fin k → ZMod 2) :
    Finset.univ.sum (fun i => if ind i = 1 then bsm.row i else 0) =
      (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  ext j
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.X i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.X.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).1 j := by
            rfl
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.Z i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.Z.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).2 j := by
            rfl

/-- The span of the checks: the stabilizer group they generate, read modulo phases. -/
def BinSympMatrix.rowSpace {k n : ℕ} (B : BinSympMatrix k n) :=
  Submodule.span (ZMod 2) (Set.range B.row)

/-- Membership in the row space is witnessed by the coefficients of a combination of checks. -/
lemma BinSympMatrix.mem_rowSpace_iff_exists_indicator {k n : ℕ} (B : BinSympMatrix k n)
    (bsp : SympSpace n) :
    bsp ∈ B.rowSpace ↔ ∃ ind : Fin k → ZMod 2,
      (B.X.transpose.mulVec ind, B.Z.transpose.mulVec ind) = bsp := by
  refine' ⟨_, fun h ↦ _⟩
  · intro h
    refine' Submodule.span_induction _ _ _ _ h
    · rintro _ ⟨i, rfl⟩
      use Pi.single i 1
      simp +decide
      rfl
    · exact ⟨0, by simp +decide⟩
    · rintro x y hx hy ⟨ind₁, rfl⟩ ⟨ind₂, rfl⟩
      use ind₁ + ind₂
      simp +decide [Matrix.mulVec_add]
    · rintro a x hx ⟨ind, rfl⟩
      use a • ind
      simp +decide [Matrix.mulVec_smul]
  · obtain ⟨ind, rfl⟩ := h
    convert Submodule.sum_mem _ _ using 1
    convert BinSympMatrix.selectedRows_sum_eq_mulVec B ind |> Eq.symm
    intro i hi
    split_ifs <;> [exact Submodule.subset_span (Set.mem_range_self i); exact Submodule.zero_mem _]

/-- An error is undetectable when it commutes with every check yet is not a product of them. -/
def BinSympMatrix.undetectable {k n : ℕ} (B : BinSympMatrix k n) (bsp : SympSpace n) : Prop :=
  (∀ i, sympForm n (B.row i) bsp = 0) ∧ bsp ∉ B.rowSpace

/-- Being undetectable is decidable, so the undetectable errors form a `Finset`. -/
noncomputable instance {k n : ℕ} (B : BinSympMatrix k n) :
    DecidablePred fun E => B.undetectable E :=
  Classical.decPred _

/-- The undetectable errors. -/
noncomputable def BinSympMatrix.undetectableSet {k n : ℕ} (B : BinSympMatrix k n) :
    Finset (SympSpace n) :=
  {bsp | B.undetectable bsp}

/-- The least weight of an undetectable error, and `n + 1` when there is none. -/
noncomputable def BinSympMatrix.distance {k n : ℕ} (B : BinSympMatrix k n) (_hk : 0 < k) : ℕ :=
  match Finset.min (B.undetectableSet.image symWeight) with
  | ⊤ => n + 1
  | some d => d

/-- A distance of at most `n` means some error really is undetectable. -/
theorem BinSympMatrix.undetectableSet_nonempty {k n : ℕ} (B : BinSympMatrix k n) (hk : 0 < k)
    (h_dist : B.distance hk ≤ n) : B.undetectableSet.Nonempty := by
  by_contra h_empty
  rw [Finset.not_nonempty_iff_eq_empty] at h_empty
  unfold BinSympMatrix.distance at h_dist
  rw [h_empty] at h_dist
  simp at h_dist

end QuantumLib
