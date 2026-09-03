/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumLib.QECC.BitVec.Stabilizer.Basic
import QuantumLib.QECC.Isotropic

/-!
# The symplectic bridge

`BinSympPauli n`, the binary symplectic space of the `BitVec` development, and
`QuantumLib.PauliOp.SympSpace n` are literally the same type, and this file shows that the two
developments put the same structure on it: `symplecticProd` is `sympForm`, `BinSympPauli.weight`
is the weight of the corresponding Pauli operator, the row space of a check matrix and the
symplectic image of a `StabCode` are isotropic subspaces, and "undetectable" is "logical".

Since a stabilizer group is recoverable from its isotropic subspace
(`QuantumLib.PauliOp.exists_stabGroup_symImage_eq`), each of the two `BitVec` presentations of a
code — a `BinSympMatrix` of checks, or a `StabCode` given by a subgroup of the Pauli group — turns
into a `QuantumLib.PauliOp.StabGroup` with the same number of logical qubits and the same distance.
No commutation-with-`-1` side condition is needed, because the stabilizer group is rebuilt from
scratch rather than read off the given generators.

The two conventions for the distance of a code with no undetectable errors disagree (`sInf ∅ = 0`
against the `n + 1` fallback of the `Finset.min` here), so the transfer theorems ask for a code
that has an undetectable error; `undetectable_set_nonempty_of_finrank_lt` and
`StabCode.undetectable_set_nonempty_of_numGenerators_lt` supply that from `k > 0`.
-/

open Module
open QuantumLib.PauliOp

variable {n k : ℕ}

/-! ### The symplectic form and the weight -/

/-- The two developments' symplectic forms are the same function. -/
theorem symplecticProd_eq_sympForm (bp₁ bp₂ : BinSympPauli n) :
    symplecticProd bp₁ bp₂ = sympForm n bp₁ bp₂ := by
  rw [sympForm_apply, Finset.sum_add_distrib]
  rfl

theorem BinSympPauli.form_eq_sympForm (n : ℕ) : BinSympPauli.form n = sympForm n :=
  LinearMap.ext fun u => LinearMap.ext fun v => by
    rw [BinSympPauli.form_apply, symplecticProd_eq_sympForm]

/-- The union weight of a binary symplectic vector is the weight of the Pauli operator it names. -/
theorem BinSympPauli.weight_eq_weight_ofSym (bp : BinSympPauli n) :
    BinSympPauli.weight bp = QuantumLib.PauliOp.weight (ofSym bp) := by
  unfold BinSympPauli.weight union_weight hammingNorm QuantumLib.PauliOp.weight
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  simp only [ne_eq, ZMod2_or_eq_zero_iff, not_and_or, ofSym_x, ofSym_z]

/-! ### Check matrices -/

theorem BinSympMatrix.mem_orthogonal_rowSpace_iff (B : BinSympMatrix k n) (bp : BinSympPauli n) :
    bp ∈ (sympForm n).orthogonal B.rowSpace ↔ ∀ i, symplecticProd (B.row i) bp = 0 := by
  rw [mem_orthogonal_iff']
  refine ⟨fun h i => ?_, fun h w hw => ?_⟩
  · rw [symplecticProd_eq_sympForm]
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [BinSympMatrix.rowSpace] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [← symplecticProd_eq_sympForm]
      exact h i
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]

/-- The rows of a commuting check matrix span an isotropic subspace. -/
theorem BinSympMatrix.rowSpace_isotropic (B : BinSympMatrix k n) (h : B.isCommuting) :
    B.rowSpace ≤ (sympForm n).orthogonal B.rowSpace := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  exact (B.mem_orthogonal_rowSpace_iff _).mpr fun j => h j i

/-- Every commuting check matrix is the check matrix of a genuine stabilizer group. -/
theorem BinSympMatrix.exists_stabGroup (B : BinSympMatrix k n) (h : B.isCommuting) :
    ∃ S : StabGroup n, S.symImage = B.rowSpace :=
  exists_stabGroup_symImage_eq (B.rowSpace_isotropic h)

theorem BinSympMatrix.undetectable_iff_isLogical (B : BinSympMatrix k n) {S : StabGroup n}
    (hS : S.symImage = B.rowSpace) (bp : BinSympPauli n) :
    B.undetectable bp ↔ S.IsLogical (ofSym bp) := by
  rw [S.isLogical_ofSym_iff, hS, BinSympMatrix.undetectable, B.mem_orthogonal_rowSpace_iff]

theorem BinSympMatrix.undetectable_set_nonempty_of_finrank_lt (B : BinSympMatrix k n)
    (h : finrank (ZMod 2) B.rowSpace < n) : B.undetectable_set.Nonempty := by
  classical
  obtain ⟨u, hu, hu'⟩ := exists_mem_orthogonal_not_mem (V := B.rowSpace) h
  have hu'' : B.undetectable u := ⟨(B.mem_orthogonal_rowSpace_iff u).mp hu, hu'⟩
  exact ⟨u, by simpa [BinSympMatrix.undetectable_set] using hu''⟩

/-- The `Finset.min`-with-fallback distance is pinned down by a least element. -/
theorem BinSympMatrix.distance_eq_of_isLeast (B : BinSympMatrix k n) (hk : 0 < k) {d : ℕ}
    (hd : d ∈ B.undetectable_set.image BinSympPauli.weight)
    (hle : ∀ a ∈ B.undetectable_set.image BinSympPauli.weight, d ≤ a) :
    B.distance hk = d := by
  unfold BinSympMatrix.distance
  cases hmin : Finset.min (B.undetectable_set.image BinSympPauli.weight) with
  | top => exact absurd (Finset.min_eq_top.mp hmin ▸ hd) (Finset.notMem_empty d)
  | coe a =>
    exact le_antisymm (WithTop.coe_le_coe.mp (hmin ▸ Finset.min_le hd))
      (hle a (Finset.mem_of_min hmin))

/-- **The distance transfers.** -/
theorem BinSympMatrix.stabGroup_distance (B : BinSympMatrix k n) {S : StabGroup n}
    (hS : S.symImage = B.rowSpace) (hk : 0 < k) (hne : B.undetectable_set.Nonempty) :
    S.distance = B.distance hk := by
  classical
  have hmem : ∀ bp : BinSympPauli n, bp ∈ B.undetectable_set ↔ B.undetectable bp := fun bp => by
    simp [BinSympMatrix.undetectable_set]
  obtain ⟨d, hd, hdle⟩ : ∃ d, d ∈ B.undetectable_set.image BinSympPauli.weight ∧
      ∀ a ∈ B.undetectable_set.image BinSympPauli.weight, d ≤ a :=
    ⟨_, Finset.min'_mem _ (hne.image _), fun a ha => Finset.min'_le _ a ha⟩
  rw [B.distance_eq_of_isLeast hk hd hdle]
  refine StabGroup.distance_eq S d ?_ ?_
  · obtain ⟨bp, hbp, hw⟩ := Finset.mem_image.mp hd
    exact ⟨ofSym bp, (B.undetectable_iff_isLogical hS bp).mp ((hmem bp).mp hbp),
      by rw [← BinSympPauli.weight_eq_weight_ofSym, hw]⟩
  · intro P hP
    have hu : B.undetectable (symOf P) :=
      (B.undetectable_iff_isLogical hS (symOf P)).mpr (S.isLogical_ofSym_symOf.mpr hP)
    have h2 := hdle _ (Finset.mem_image_of_mem _ ((hmem _).mpr hu))
    rwa [BinSympPauli.weight_eq_weight_ofSym, weight_ofSym_symOf] at h2

/-- **A check matrix names a stabilizer code.** A commuting check matrix that leaves at least one
symplectic dimension free defines a `StabGroup` with the expected number of logical qubits and
exactly the distance computed from the matrix. -/
theorem BinSympMatrix.exists_stabGroup_params (B : BinSympMatrix k n) (hcomm : B.isCommuting)
    (hk : 0 < k) (hrk : finrank (ZMod 2) B.rowSpace < n) :
    ∃ S : StabGroup n, S.numLogical = n - finrank (ZMod 2) B.rowSpace ∧
      S.distance = B.distance hk := by
  obtain ⟨S, hS⟩ := B.exists_stabGroup hcomm
  exact ⟨S, by rw [S.numLogical_eq, hS],
    B.stabGroup_distance hS hk (B.undetectable_set_nonempty_of_finrank_lt hrk)⟩

/-! ### Codes given as subgroups of the Pauli group -/

theorem StabCode.stabSymplecticSpace_isotropic (C : StabCode n) :
    C.stabSymplecticSpace ≤ (sympForm n).orthogonal C.stabSymplecticSpace := by
  simpa [StabCode.normalizerSpace, BinSympPauli.form_eq_sympForm] using
    C.stabSymplecticSpace_le_normalizerSpace

theorem StabCode.exists_stabGroup (C : StabCode n) :
    ∃ S : StabGroup n, S.symImage = C.stabSymplecticSpace :=
  exists_stabGroup_symImage_eq C.stabSymplecticSpace_isotropic

theorem StabCode.mem_normalizerGroup_iff_mem_orthogonal (C : StabCode n) (E : PauliGroup n) :
    E ∈ C.normalizerGroup ↔
      Pauli_toBinSympPauli E ∈ (sympForm n).orthogonal C.stabSymplecticSpace := by
  rw [C.mem_normalizerGroup_iff_symplecticProd, mem_orthogonal_iff']
  refine ⟨fun h w hw => ?_, fun h s hs => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := (C.mem_stabilizerSpace_iff w).1 hw
    rw [← symplecticProd_eq_sympForm]
    exact h s hs
  · rw [symplecticProd_eq_sympForm]
    exact h _ ((C.mem_stabilizerSpace_iff _).2 ⟨s, hs, rfl⟩)

theorem StabCode.mem_trivialLogicals_iff_mem_stabSymplecticSpace (C : StabCode n)
    (E : PauliGroup n) :
    E ∈ C.trivialLogicals ↔ Pauli_toBinSympPauli E ∈ C.stabSymplecticSpace :=
  (C.mem_trivialLogicals_iff E).trans (C.mem_stabilizerSpace_iff _).symm

theorem StabCode.undetectable_iff_isLogical (C : StabCode n) {S : StabGroup n}
    (hS : S.symImage = C.stabSymplecticSpace) (E : PauliGroup n) :
    C.undetectable E ↔
      S.IsLogical (ofSym (Pauli_toBinSympPauli E)) ∧ PauliGroup.normalized E := by
  rw [StabCode.undetectable, S.isLogical_ofSym_iff, hS,
    C.mem_normalizerGroup_iff_mem_orthogonal, C.mem_trivialLogicals_iff_mem_stabSymplecticSpace]
  tauto

theorem StabCode.numGenerators_eq_finrank (C : StabCode n) {S : StabGroup n}
    (hS : S.symImage = C.stabSymplecticSpace) :
    C.numGenerators = finrank (ZMod 2) S.symImage := by
  rw [StabCode.numGenerators, hS]

theorem StabCode.numLogical_eq_of_symImage (C : StabCode n) {S : StabGroup n}
    (hS : S.symImage = C.stabSymplecticSpace) : S.numLogical = n - C.numGenerators := by
  rw [S.numLogical_eq, C.numGenerators_eq_finrank hS]

theorem StabCode.undetectable_set_nonempty_of_numGenerators_lt (C : StabCode n)
    (h : C.numGenerators < n) : C.undetectable_set.Nonempty := by
  classical
  obtain ⟨S, hS⟩ := C.exists_stabGroup
  obtain ⟨P, hP⟩ := StabGroup.exists_isLogical_of_finrank_lt (S := S)
    (by rwa [← C.numGenerators_eq_finrank hS])
  have hu : C.undetectable (BinSympPauli_toPauli (symOf P)) := by
    refine (C.undetectable_iff_isLogical hS _).mpr ⟨?_, BinSympPauli_toPauli_normalized _⟩
    rwa [Pauli_toBinSympPauli_BinSympPauli_toPauli, S.isLogical_ofSym_symOf]
  exact ⟨_, by simpa [StabCode.undetectable_set] using hu⟩

theorem StabCode.distance_eq_of_isLeast (C : StabCode n) {d : ℕ}
    (hd : d ∈ C.undetectable_set.image pauli_weight)
    (hle : ∀ a ∈ C.undetectable_set.image pauli_weight, d ≤ a) :
    C.distance = d := by
  unfold StabCode.distance
  cases hmin : Finset.min (C.undetectable_set.image pauli_weight) with
  | top => exact absurd (Finset.min_eq_top.mp hmin ▸ hd) (Finset.notMem_empty d)
  | coe a =>
    exact le_antisymm (WithTop.coe_le_coe.mp (hmin ▸ Finset.min_le hd))
      (hle a (Finset.mem_of_min hmin))

/-- **The distance transfers.** -/
theorem StabCode.stabGroup_distance (C : StabCode n) {S : StabGroup n}
    (hS : S.symImage = C.stabSymplecticSpace) (hne : C.undetectable_set.Nonempty) :
    S.distance = C.distance := by
  classical
  have hmem : ∀ E : PauliGroup n, E ∈ C.undetectable_set ↔ C.undetectable E := fun E => by
    simp [StabCode.undetectable_set]
  obtain ⟨d, hd, hdle⟩ : ∃ d, d ∈ C.undetectable_set.image pauli_weight ∧
      ∀ a ∈ C.undetectable_set.image pauli_weight, d ≤ a :=
    ⟨_, Finset.min'_mem _ (hne.image _), fun a ha => Finset.min'_le _ a ha⟩
  rw [C.distance_eq_of_isLeast hd hdle]
  refine StabGroup.distance_eq S d ?_ ?_
  · obtain ⟨E, hE, hw⟩ := Finset.mem_image.mp hd
    refine ⟨ofSym (Pauli_toBinSympPauli E),
      ((C.undetectable_iff_isLogical hS E).mp ((hmem E).mp hE)).1, ?_⟩
    rw [← BinSympPauli.weight_eq_weight_ofSym, ← pauli_weight_eq_BinSympPauli_weight, hw]
  · intro P hP
    have hu : C.undetectable (BinSympPauli_toPauli (symOf P)) := by
      refine (C.undetectable_iff_isLogical hS _).mpr ⟨?_, BinSympPauli_toPauli_normalized _⟩
      rwa [Pauli_toBinSympPauli_BinSympPauli_toPauli, S.isLogical_ofSym_symOf]
    have h2 := hdle _ (Finset.mem_image_of_mem _ ((hmem _).mpr hu))
    rwa [pauli_weight_BinSympPauli_toPauli, BinSympPauli.weight_eq_weight_ofSym,
      weight_ofSym_symOf] at h2

/-- **A `⟦n, k, d⟧` code in the `BitVec` formulation is a `⟦n, k, d⟧` stabilizer group.** -/
theorem param_triple.exists_stabGroup {C : StabCode n} {k d : ℕ} (h : param_triple C k d)
    (hk : 0 < k) : ∃ S : StabGroup n, S.numLogical = k ∧ d ≤ S.distance := by
  have hkg : k = n - C.numGenerators := (C.dim_iff_generators k).1 h.achieves_k
  have hlt : C.numGenerators < n := by
    have := C.numGenerators_le
    omega
  obtain ⟨S, hS⟩ := C.exists_stabGroup
  refine ⟨S, by rw [C.numLogical_eq_of_symImage hS, ← hkg], ?_⟩
  rw [C.stabGroup_distance hS (C.undetectable_set_nonempty_of_numGenerators_lt hlt)]
  exact h.achieves_d
