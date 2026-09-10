/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Yi Lee
-/

import Mathlib.Data.BitVec
import QuantumLib.QECC.BitVec.LinearAlgebra.RowspaceKernel
import Init.Data.BitVec.Basic

/-!
# Propositional encoding of code properties

The `BitVec` predicates behind the SAT queries. A `k × n` matrix over `ZMod 2` is flattened into a
`BitVec (k * n)`, and an error of weight at most `dist` is described by its `dist` support indices
packed into a `BitVec (dist * nlog)`. The solver is asked to refute the existence of such an error
that is in the kernel of one matrix but outside the row space of another, and `ltDistSat` is that
refutation. There are also encodings of linear independence (`linearIndepSAT`) and of row
orthogonality (`bitVecMutuallyOrthNat`).
-/

namespace QuantumLib

/-- The `j`-th of the positions packed into `locs` is `i`. Each position takes an `nlog`-bit
field, `nlog` being `⌈log₂ n⌉`, enough bits to name any of the `n` qubits. -/
@[simp]
def locConstraintsIthJth
    {nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (i j : ℕ) :=
  ((locs.extractLsb' (j * nlog) nlog) = i)

/-- One of the positions `0, …, j` packed into `locs` is `i`. -/
@[simp]
def locConstraintsIthJthAux
    {nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (i j : ℕ) :=
  match j with
  | 0 => locConstraintsIthJth locs i 0
  | j' + 1 => locConstraintsIthJth locs i j ∨
              locConstraintsIthJthAux locs i j'

/-- The error `errs` acts on qubit `i` exactly when `i` is one of the `k` positions packed into
`locs`. -/
@[simp]
def locConstraintsIth
    {n nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (errs : BitVec n)
    (i : ℕ) :=
  errs[i]! = locConstraintsIthJthAux locs i (k-1)

/-- `locConstraintsIth` for each of the qubits `0, …, c`. -/
@[simp]
def locConstraintsAux
    {n nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (errs : BitVec n)
    (c : ℕ) :=
  match c with
  | 0 => locConstraintsIth locs errs 0
  | c' + 1 =>
    locConstraintsIth locs errs c ∧
    locConstraintsAux locs errs c'

/-- `errs` is supported exactly on the `k` positions packed into `locs`, and so has weight at
most `k`. -/
def locConstraints
    {n nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (errs : BitVec n) :=
  locConstraintsAux locs errs (n-1)

/-- The positions `0, …, c` packed into `locs` increase weakly, the last of them being at most
`prev`. -/
def symmetryConstraintsAux
    {nlog k : ℕ}
    (locs : BitVec (k * nlog))
    (c : ℕ) (prev : BitVec nlog) : Bool :=
  let val := locs.extractLsb' (c * nlog) nlog
  match c with
  | 0 => val ≤ prev
  | c' + 1 => (val ≤ prev) && (symmetryConstraintsAux locs c' val)

/-- The `k` positions packed into `locs` are in non-decreasing order. This breaks the symmetry
under permuting them, which would otherwise multiply the search space by `k!`. -/
def symmetryConstraints
    {nlog k : ℕ}
    (locs : BitVec (k * nlog)) :=
  symmetryConstraintsAux locs (k - 1) (BitVec.allOnes nlog)

/-- The parity of `x &&& y` over the bits `0, …, c`. -/
def dotProductAux {n : ℕ} [NeZero n] (x y : BitVec n) (c : ℕ) (hc : c < n) : Bool :=
  let b := x[c] && y[c]
  match c with
  | 0 => b
  | c' + 1 => b ^^ dotProductAux x y c' (lt_of_le_of_lt (Nat.le_succ _) hc)

/-- The `ZMod 2` inner product of two bit vectors: the parity of their bitwise `and`. -/
def _root_.BitVec.dotProduct {n : ℕ} [NeZero n] (x y : BitVec n) :=
  dotProductAux x y (n-1) (Nat.sub_one_lt (NeZero.ne _))

/-- The `r`-th row of a `k × n` matrix flattened into a `BitVec (k * n)`, one row after another. -/
def _root_.BitVec.row {n k : ℕ} (M : BitVec (k * n)) (r : ℕ) : BitVec n := (M >>> (r * n)).extractLsb' 0 n

/-- `errs` is orthogonal to the rows `0, …, r` of `stabs`. -/
@[simp]
def parityConstraintsAux {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => !(errs.dotProduct (stabs.row 0))
  | r' + 1 => !(errs.dotProduct (stabs.row r)) ∧ parityConstraintsAux stabs errs r'

/-- `errs` is orthogonal to every check, that is, no check detects it. -/
def parityConstraints {stabdim n : ℕ} [NeZero n] (stabs : BitVec (stabdim * n)) (errs : BitVec n) :=
  parityConstraintsAux stabs errs (stabdim-1)

/-- `errs` is non-orthogonal to one of the rows `0, …, r` of `ker`. -/
@[simp]
def rowspaceConstraintsAux
    {kerdim n : ℕ}
    [NeZero n]
    (ker : BitVec (kerdim * n))
    (errs : BitVec n) (r : ℕ) :=
  match r with
  | 0 => (errs.dotProduct (ker.row 0))
  | r' + 1 => (errs.dotProduct (ker.row r)) ∨
      rowspaceConstraintsAux ker errs r'

/-- `errs` is non-orthogonal to some row of `ker`. When the rows of `ker` span the kernel of a
check matrix, this says exactly that `errs` lies outside that matrix's row space. -/
def rowspaceConstraints
    {kerdim n : ℕ}
    [NeZero n]
    (ker : BitVec (kerdim * n))
    (errs : BitVec n) :=
  rowspaceConstraintsAux ker errs (kerdim - 1)

/-- No error of weight at most `k` is undetectable: no `errs` supported on `k` positions, each
named by `nlog` bits, is orthogonal to every row of `stabs` while failing to be orthogonal to
every row of `ker`. -/
def ltDistSat
    {n stabdim kerdim : ℕ}
    [NeZero n]
    (stabs : BitVec (stabdim * n))
    (ker : BitVec (kerdim * n))
    (k nlog : ℕ) : Prop :=
  ∀ (locs : (BitVec (k * nlog))) (errs : BitVec n),
  ¬ (locConstraints locs errs ∧ symmetryConstraints locs ∧ parityConstraints stabs errs ∧
    rowspaceConstraints ker errs)

/-- Row `i` of `M₁` is orthogonal to the rows `0, …, j` of `M₂`. -/
def mutuallyOrthRowSatAux
    {n k₁ k₂ : ℕ}
    [NeZero n]
    (M₁ : BitVec (k₁ * n))
    (M₂ : BitVec (k₂ * n))
    (i j : ℕ) : Bool :=
  match j with
  | 0 => !((M₁.row i).dotProduct (M₂.row 0))
  | j' + 1 => !((M₁.row i).dotProduct (M₂.row j)) && mutuallyOrthRowSatAux M₁ M₂ i j'

/-- The rows `0, …, i` of `M₁` are orthogonal to every row of `M₂`. -/
def mutuallyOrthSatAux
    {n k₁ k₂ : ℕ}
    [NeZero n]
    [NeZero k₂]
    (M₁ : BitVec (k₁ * n))
    (M₂ : BitVec (k₂ * n))
    (i : ℕ) : Bool :=
  match i with
  | 0 => mutuallyOrthRowSatAux M₁ M₂ 0 (k₂ - 1)
  | i' + 1 => mutuallyOrthRowSatAux M₁ M₂ i (k₂ - 1) && mutuallyOrthSatAux M₁ M₂ i'

/-- Every row of `M₁` is orthogonal to every row of `M₂`, for matrices flattened into bit
vectors. -/
def bitVecMutuallyOrthNat
    {n k₁ k₂ : ℕ}
    [NeZero n]
    [NeZero k₁]
    [NeZero k₂]
    (M₁ : BitVec (k₁ * n))
    (M₂ : BitVec (k₂ * n)) : Prop :=
  mutuallyOrthSatAux M₁ M₂ (k₁ - 1)

/-- One of the bits `0, …, i` of `coeffs` is set. -/
@[simp]
def nonzeroAux {r : ℕ} (coeffs : BitVec r) (i : ℕ) :=
  match i with
  | 0 => coeffs[0]!
  | i₀ + 1 => (coeffs[i]!) ∨ nonzeroAux coeffs i₀

/-- `coeffs` is not zero. -/
@[simp]
def nonzero {r : ℕ} (coeffs : BitVec r) := nonzeroAux coeffs (r-1)

/-- Entry `c` of the combination of the rows `0, …, i` of `mat` with coefficients `coeffs`. -/
@[simp]
def dotColAux {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) (i : ℕ) :=
  let k := i * n + c
  match i with
  | 0 => coeffs[i]! && mat[k]!
  | i₀ + 1 => (coeffs[i]! && mat[k]!) ^^ dotColAux coeffs mat c i₀

/-- The combination of the rows of `mat` with coefficients `coeffs` vanishes in column `c`. -/
@[simp]
def dotColZero {n r : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  let dot := dotColAux coeffs mat c (r-1)
  !dot

/-- The combination of the rows of `mat` with coefficients `coeffs` vanishes in the columns
`0, …, c`. -/
@[simp]
def allDotZeroAux {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) (c : ℕ) :=
  match c with
  | 0 => (dotColZero coeffs mat 0)
  | c₀ + 1 => dotColZero coeffs mat c && allDotZeroAux coeffs mat c₀

/-- The combination of the rows of `mat` with coefficients `coeffs` is zero. -/
@[simp]
def allDotZero {r n : ℕ} (coeffs : BitVec r) (mat : BitVec (r * n)) := allDotZeroAux coeffs mat (n-1)

/-- No nonzero combination of the rows of `mat` vanishes, that is, the rows are linearly
independent. -/
def linearIndepSAT {r n : ℕ} (mat : BitVec (r * n)) : Prop := ∀ coeffs, !(nonzero coeffs && allDotZero coeffs mat)

/-- The indices `inds 0, …, inds i` are strictly increasing, the last of them below `prev`. -/
def indsStrictMonoAux {k r : ℕ} (inds : Fin r → Fin k) (i : Fin r) (prev : ℕ) : Bool :=
  let b := (inds i).1.blt prev
  match i with
  | ⟨0, _⟩ => b
  | ⟨i' + 1, h⟩ => b && (indsStrictMonoAux inds ⟨i', (Nat.lt_succ_self _).trans h⟩ (inds i).1)

/-- The indices `inds` are strictly increasing. -/
def indsStrictMono {k r : ℕ} [NeZero r] (inds : Fin r → Fin k) : Prop :=
  indsStrictMonoAux inds ⟨r-1, Nat.sub_one_lt (NeZero.ne _)⟩ k

end QuantumLib
