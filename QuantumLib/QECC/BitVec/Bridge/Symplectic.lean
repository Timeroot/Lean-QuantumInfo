/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.BitVec.Stabilizer.Basic
import QuantumLib.QECC.Isotropic

/-!
# The symplectic bridge

The `BitVec` development and `QuantumLib.PauliOp` share a symplectic space, a symplectic form and
a weight; what remains is to identify the code-theoretic notions the two build on top of them. The
row space of a commuting check matrix is an isotropic subspace, and "undetectable" is "logical".

Since a stabilizer group is recoverable from its isotropic subspace
(`QuantumLib.PauliOp.exists_stabGroup_symImage_eq`), a `BinSympMatrix` of commuting checks names a
`QuantumLib.PauliOp.StabGroup` with a known number of logical qubits and a known distance. No
commutation-with-`-1` side condition is needed, because the stabilizer group is rebuilt from
scratch rather than read off the given generators, and neither is independence of the rows.

The two conventions for the distance of a code with no undetectable errors disagree (`sInf ∅ = 0`
against the `n + 1` fallback of the `Finset.min` here), so the transfer theorems ask for a code
that has an undetectable error; `undetectableSet_nonempty_of_finrank_lt` supplies that from
`k > 0`.
-/

open Module
open QuantumLib.PauliOp

namespace QuantumLib

variable {m n : ℕ}

/-! ### Check matrices -/

/-- A point is symplectically orthogonal to the whole row space exactly when it commutes with
every check. -/
theorem BinSympMatrix.mem_orthogonal_rowSpace_iff (B : BinSympMatrix m n) (bp : SympSpace n) :
    bp ∈ (sympForm n).orthogonal B.rowSpace ↔ ∀ i, sympForm n (B.row i) bp = 0 := by
  rw [mem_orthogonal_iff']
  refine ⟨fun h i => h _ (Submodule.subset_span ⟨i, rfl⟩), fun h w hw => ?_⟩
  rw [BinSympMatrix.rowSpace] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-- The rows of a commuting check matrix span an isotropic subspace. -/
theorem BinSympMatrix.rowSpace_isotropic (B : BinSympMatrix m n) (h : B.isCommuting) :
    B.rowSpace ≤ (sympForm n).orthogonal B.rowSpace := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact (B.mem_orthogonal_rowSpace_iff _).mpr fun j => h j i

/-- Every commuting check matrix is the check matrix of a genuine stabilizer group. -/
theorem BinSympMatrix.exists_stabGroup (B : BinSympMatrix m n) (h : B.isCommuting) :
    ∃ S : StabGroup n, S.symImage = B.rowSpace :=
  exists_stabGroup_symImage_eq (B.rowSpace_isotropic h)

/-- An error is undetectable exactly when it is a logical operator of the stabilizer group the
checks name. -/
theorem BinSympMatrix.undetectable_iff_isLogical (B : BinSympMatrix m n) {S : StabGroup n}
    (hS : S.symImage = B.rowSpace) (bp : SympSpace n) :
    B.undetectable bp ↔ S.IsLogical (ofSym bp) := by
  rw [S.isLogical_ofSym_iff, hS, BinSympMatrix.undetectable, B.mem_orthogonal_rowSpace_iff]

/-- A row space of dimension below `n` leaves an undetectable error, so the code has logical
operators. -/
theorem BinSympMatrix.undetectableSet_nonempty_of_finrank_lt (B : BinSympMatrix m n)
    (h : finrank (ZMod 2) B.rowSpace < n) : B.undetectableSet.Nonempty := by
  classical
  obtain ⟨u, hu, hu'⟩ := exists_mem_orthogonal_not_mem (V := B.rowSpace) h
  have hu'' : B.undetectable u := ⟨(B.mem_orthogonal_rowSpace_iff u).mp hu, hu'⟩
  exact ⟨u, by simpa [BinSympMatrix.undetectableSet] using hu''⟩

/-- The `Finset.min`-with-fallback distance is pinned down by a least element. -/
theorem BinSympMatrix.distance_eq_of_isLeast (B : BinSympMatrix m n) (hm : 0 < m) {d : ℕ}
    (hd : d ∈ B.undetectableSet.image symWeight)
    (hle : ∀ a ∈ B.undetectableSet.image symWeight, d ≤ a) :
    B.distance hm = d := by
  unfold BinSympMatrix.distance
  cases hmin : Finset.min (B.undetectableSet.image symWeight) with
  | top => exact absurd (Finset.min_eq_top.mp hmin ▸ hd) (Finset.notMem_empty d)
  | coe a =>
    exact le_antisymm (WithTop.coe_le_coe.mp (hmin ▸ Finset.min_le hd))
      (hle a (Finset.mem_of_min hmin))

/-- **The distance transfers.** -/
theorem BinSympMatrix.stabGroup_distance (B : BinSympMatrix m n) {S : StabGroup n}
    (hS : S.symImage = B.rowSpace) (hm : 0 < m) (hne : B.undetectableSet.Nonempty) :
    S.distance = B.distance hm := by
  classical
  have hmem : ∀ bp : SympSpace n, bp ∈ B.undetectableSet ↔ B.undetectable bp := fun bp => by
    simp [BinSympMatrix.undetectableSet]
  obtain ⟨d, hd, hdle⟩ : ∃ d, d ∈ B.undetectableSet.image symWeight ∧
      ∀ a ∈ B.undetectableSet.image symWeight, d ≤ a :=
    ⟨_, Finset.min'_mem _ (hne.image _), fun a ha => Finset.min'_le _ a ha⟩
  rw [B.distance_eq_of_isLeast hm hd hdle]
  refine StabGroup.distance_eq S d ?_ ?_
  · obtain ⟨bp, hbp, hw⟩ := Finset.mem_image.mp hd
    exact ⟨ofSym bp, (B.undetectable_iff_isLogical hS bp).mp ((hmem bp).mp hbp),
      by rw [weight_ofSym, hw]⟩
  · intro P hP
    have hu : B.undetectable (symOf P) :=
      (B.undetectable_iff_isLogical hS (symOf P)).mpr (S.isLogical_ofSym_symOf.mpr hP)
    have h2 := hdle _ (Finset.mem_image_of_mem _ ((hmem _).mpr hu))
    rwa [symWeight_symOf] at h2

/-! ### Code parameters -/

/-- **`B` is the check matrix of an `⟦n, k, d⟧` code**: some stabilizer group has the rows of `B`
as its symplectic image, `k` logical qubits and distance at least `d`. -/
def BinSympMatrix.IsCode (B : BinSympMatrix m n) (k d : ℕ) : Prop :=
  ∃ S : StabGroup n, S.symImage = B.rowSpace ∧ S.numLogical = k ∧ d ≤ S.distance

/-- A commuting check matrix whose row space has corank `k > 0` is the check matrix of an
`⟦n, k, d⟧` code, for any `d` below the distance computed from the matrix. -/
theorem BinSympMatrix.isCode_of (B : BinSympMatrix m n) (hcomm : B.isCommuting) (hm : 0 < m)
    {k d : ℕ} (hk : k = n - finrank (ZMod 2) B.rowSpace) (hkpos : 0 < k)
    (hd : d ≤ B.distance hm) : B.IsCode k d := by
  obtain ⟨S, hS⟩ := B.exists_stabGroup hcomm
  have hle : finrank (ZMod 2) B.rowSpace ≤ n := hS ▸ S.finrank_symImage_le
  refine ⟨S, hS, by rw [S.numLogical_eq, hS, hk], ?_⟩
  rw [B.stabGroup_distance hS hm (B.undetectableSet_nonempty_of_finrank_lt (by omega))]
  exact hd

end QuantumLib
