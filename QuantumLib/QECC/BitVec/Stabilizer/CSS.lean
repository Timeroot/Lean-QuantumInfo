/-
Copyright (c) 2026 The Lean-QEC Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mattias Ehatamm, Runzhou Tao, Yi Lee, Eashan Hatti
-/

import QuantumLib.QECC.BitVec.Bridge.Symplectic
import QuantumLib.QECC.BitVec.Classical.CodeSpace

/-!
# CSS codes

A `CSSPair n k₁ k₂` is a pair of parity-check matrices over `ZMod 2` with orthogonal row spaces.
This file assembles them into a `BinSympMatrix` of commuting checks, identifies its `X` and `Z`
distances with the minimum weights of kernel vectors outside the opposite row space, shows that
the distance of the code is the smaller of the two, and counts the logical qubits.
-/

open QuantumLib.PauliOp

namespace QuantumLib

variable {n k₁ k₂ : ℕ}

/-- The check matrix of a CSS code: the rows of `H₁` become `Z`-type checks and the rows of `H₂`
`X`-type checks, so the two blocks never overlap. -/
def cssBSM (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : BinSympMatrix (k₁ + k₂) n where
  X := Fin.append (fun (_ : Fin k₁) => (fun _ => 0)) H₂
  Z := Fin.append H₁ (fun (_ : Fin k₂) => (fun _ => 0))

@[simp] lemma cssBSM_X_castAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₁) :
    (cssBSM H₁ H₂).X (Fin.castAdd k₂ i) = 0 :=
  Fin.append_left (fun (_ : Fin k₁) => (0 : Fin n → ZMod 2)) H₂ i

@[simp] lemma cssBSM_X_natAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₂) :
    (cssBSM H₁ H₂).X (Fin.natAdd k₁ i) = H₂ i :=
  Fin.append_right (fun (_ : Fin k₁) => (0 : Fin n → ZMod 2)) H₂ i

@[simp] lemma cssBSM_Z_castAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₁) :
    (cssBSM H₁ H₂).Z (Fin.castAdd k₂ i) = H₁ i :=
  Fin.append_left H₁ (fun (_ : Fin k₂) => (0 : Fin n → ZMod 2)) i

@[simp] lemma cssBSM_Z_natAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₂) :
    (cssBSM H₁ H₂).Z (Fin.natAdd k₁ i) = 0 :=
  Fin.append_right H₁ (fun (_ : Fin k₂) => (0 : Fin n → ZMod 2)) i

@[simp] lemma cssBSM_row_castAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₁) :
    (cssBSM H₁ H₂).row (Fin.castAdd k₂ i) = (0, H₁ i) := by
  show ((cssBSM H₁ H₂).X (Fin.castAdd k₂ i), (cssBSM H₁ H₂).Z (Fin.castAdd k₂ i)) = _
  rw [cssBSM_X_castAdd, cssBSM_Z_castAdd]

@[simp] lemma cssBSM_row_natAdd (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (i : Fin k₂) :
    (cssBSM H₁ H₂).row (Fin.natAdd k₁ i) = (H₂ i, 0) := by
  show ((cssBSM H₁ H₂).X (Fin.natAdd k₁ i), (cssBSM H₁ H₂).Z (Fin.natAdd k₁ i)) = _
  rw [cssBSM_X_natAdd, cssBSM_Z_natAdd]

/-- A CSS code on `n` bits: two classical codes with `C₁ᗮ ⊆ C₂`, each presented by a parity check
matrix, and at least one check of each type. -/
structure CSSPair (n k₁ k₂) where
  /-- The code whose parity checks become `Z`-type stabilizers. -/
  C₁ : CodeSpace n
  /-- The code whose parity checks become `X`-type stabilizers. -/
  C₂ : CodeSpace n
  H_dual : (C₁.dualCode : Set (Fin n → ZMod 2)) ⊆ C₂
  /-- A parity check matrix for `C₁`, with `k₁` checks. -/
  H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)
  /-- A parity check matrix for `C₂`, with `k₂` checks. -/
  H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)
  hpc₁ : C₁.parityCheckedBy H₁
  hpc₂ : C₂.parityCheckedBy H₂
  nt₁ : 0 < k₁
  nt₂ : 0 < k₂

/-- The checks of a CSS code, as a binary symplectic matrix. -/
def CSSPair.toBSM (C : CSSPair n k₁ k₂) := cssBSM C.H₁ C.H₂

/-- The `X` distance: the least weight of a vector in the kernel of `H₂` outside the row space of
`H₁`. -/
noncomputable def CSSPair.dX (C : CSSPair n k₁ k₂) := minWeightKerNotMemRowspace C.H₂ C.H₁

/-- The `Z` distance: the least weight of a vector in the kernel of `H₁` outside the row space of
`H₂`. -/
noncomputable def CSSPair.dZ (C : CSSPair n k₁ k₂) := minWeightKerNotMemRowspace C.H₁ C.H₂

/-- Two finite sets of naturals, each of whose elements is bounded below by an element of the
other, have the same minimum. -/
private lemma finset_min_eq_of_forall_exists_le {s t : Finset ℕ}
    (hst : ∀ a ∈ s, ∃ b ∈ t, b ≤ a)
    (hts : ∀ b ∈ t, ∃ a ∈ s, a ≤ b) :
    s.min = t.min := by
  apply le_antisymm
  · rw [Finset.le_min_iff]
    intro b hb
    rcases hts b hb with ⟨a, ha, hab⟩
    exact (Finset.min_le ha).trans (WithTop.coe_le_coe.2 hab)
  · rw [Finset.le_min_iff]
    intro a ha
    rcases hst a ha with ⟨b, hb, hba⟩
    exact (Finset.min_le hb).trans (WithTop.coe_le_coe.2 hba)

/-- The minimum of a union, read with the fallback `n + 1`, is the smaller of the two
minima. -/
private lemma min_with_fallback_union_eq_min {s t : Finset ℕ} {n : ℕ}
    (hs : ∀ a ∈ s, a ≤ n) (ht : ∀ a ∈ t, a ≤ n) :
    (match (s ∪ t).min with
      | ⊤ => n + 1
      | some a => a) =
    min
      (match s.min with
        | ⊤ => n + 1
        | some a => a)
      (match t.min with
        | ⊤ => n + 1
        | some a => a) := by
  rw [Finset.min_union]
  cases hsmin : s.min with
  | top =>
      cases htmin : t.min with
      | top => simp
      | coe b =>
          have hb_mem : b ∈ t := Finset.mem_of_min htmin
          have hb_le : b ≤ n := ht b hb_mem
          simp
          exact Nat.le_succ_of_le hb_le
  | coe a =>
      have ha_mem : a ∈ s := Finset.mem_of_min hsmin
      have ha_le : a ≤ n := hs a ha_mem
      cases htmin : t.min with
      | top =>
          simp
          exact Nat.le_succ_of_le ha_le
      | coe b =>
          rw [← WithTop.coe_min]

/-- The row space of a CSS check matrix is the product of the two row spaces. -/
private lemma cssBSM_rowSpace_iff
    (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
    (x z : Fin n → ZMod 2) :
    (x, z) ∈ (cssBSM H₁ H₂).rowSpace ↔
      x ∈ H₂.rowSpace ∧ z ∈ H₁.rowSpace := by
  constructor
  · intro h
    let prodRows : Submodule (ZMod 2) (SympSpace n) :=
    {
      carrier := {bsp | bsp.1 ∈ H₂.rowSpace ∧ bsp.2 ∈ H₁.rowSpace}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        exact ⟨Submodule.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      smul_mem' := by
        intro a b hb
        exact ⟨Submodule.smul_mem _ a hb.1, Submodule.smul_mem _ a hb.2⟩
    }
    have hle : (cssBSM H₁ H₂).rowSpace ≤ prodRows := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · constructor
        · simp only [cssBSM_row_castAdd]
          exact Submodule.zero_mem _
        · simp only [cssBSM_row_castAdd]
          exact Matrix.row_mem_rowSpace
      · constructor
        · simp only [cssBSM_row_natAdd]
          exact Matrix.row_mem_rowSpace
        · simp only [cssBSM_row_natAdd]
          exact Submodule.zero_mem _
    exact hle h
  · rintro ⟨hx, hz⟩
    have hx_pair : (x, 0) ∈ (cssBSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (y, 0) ∈ (cssBSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.natAdd k₁ i, ?_⟩
        simp [Matrix.row_apply']
      · exact Submodule.zero_mem ((cssBSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((cssBSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((cssBSM H₁ H₂).rowSpace) a hy
    have hz_pair : (0, z) ∈ (cssBSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (0, y) ∈ (cssBSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.castAdd k₂ i, ?_⟩
        simp [Matrix.row_apply']
      · exact Submodule.zero_mem ((cssBSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((cssBSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((cssBSM H₁ H₂).rowSpace) a hy
    simpa [Prod.ext_iff] using
      Submodule.add_mem ((cssBSM H₁ H₂).rowSpace) hx_pair hz_pair

/-- The symplectic form of a pure `Z` operator against `v` pairs its `Z` part with the `X` part
of `v`. -/
private lemma sympForm_zero_fst (a : Fin n → ZMod 2) (v : SympSpace n) :
    sympForm n (0, a) v = a ⬝ᵥ v.1 := by
  rw [sympForm_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- The symplectic form of a pure `X` operator against `v` pairs its `X` part with the `Z` part
of `v`. -/
private lemma sympForm_zero_snd (a : Fin n → ZMod 2) (v : SympSpace n) :
    sympForm n (a, 0) v = a ⬝ᵥ v.2 := by
  rw [sympForm_apply, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- The weight of the `X` part is at most the symplectic weight. -/
private lemma hammingNorm_fst_le_symWeight (v : SympSpace n) : hammingNorm v.1 ≤ symWeight v := by
  unfold hammingNorm symWeight
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inl hi

/-- The weight of the `Z` part is at most the symplectic weight. -/
private lemma hammingNorm_snd_le_symWeight (v : SympSpace n) : hammingNorm v.2 ≤ symWeight v := by
  unfold hammingNorm symWeight
  refine Finset.card_le_card fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inr hi

/-- A pure `Z` operator has symplectic weight the weight of its `Z` part. -/
private lemma symWeight_zero_fst (z : Fin n → ZMod 2) :
    symWeight ((0 : Fin n → ZMod 2), z) = hammingNorm z := by
  simp [symWeight, hammingNorm]

/-- A pure `X` operator has symplectic weight the weight of its `X` part. -/
private lemma symWeight_zero_snd (x : Fin n → ZMod 2) :
    symWeight (x, (0 : Fin n → ZMod 2)) = hammingNorm x := by
  simp [symWeight, hammingNorm]

/-- The distance of a CSS code is the smaller of its `X` and `Z` distances. -/
theorem CSS.toBSM_dist_eq (C : CSSPair n k₁ k₂) :
    C.toBSM.distance (Nat.add_pos_left C.nt₁ _) = min C.dX C.dZ := by
  let xWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace).toFinset)
  let zWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace).toFinset)
  let bsmWeights : Finset ℕ :=
    Finset.image symWeight C.toBSM.undetectableSet
  have hbsm_min : bsmWeights.min = (xWeights ∪ zWeights).min := by
    apply finset_min_eq_of_forall_exists_le
    · intro d hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : C.toBSM.undetectable bsp := by
        simpa [BinSympMatrix.undetectableSet] using hbsp
      rcases hbsp' with ⟨hcomm, hnot_row⟩
      have hx_ker : bsp.1 ∈ LinearMap.ker C.H₁.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.castAdd k₂ i)
        simpa [CSSPair.toBSM, sympForm_zero_fst] using this
      have hz_ker : bsp.2 ∈ LinearMap.ker C.H₂.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.natAdd k₁ i)
        simpa [CSSPair.toBSM, sympForm_zero_snd] using this
      have hnot_or : bsp.1 ∉ C.H₂.rowSpace ∨ bsp.2 ∉ C.H₁.rowSpace := by
        by_contra h
        simp only [not_or, not_not] at h
        apply hnot_row
        exact (cssBSM_rowSpace_iff C.H₁ C.H₂ bsp.1 bsp.2).2 ⟨h.1, h.2⟩
      rcases hnot_or with hx_not | hz_not
      · refine ⟨hammingNorm bsp.1, ?_, ?_⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨bsp.1, ?_, rfl⟩
          simp [hx_ker, hx_not]
        · exact hammingNorm_fst_le_symWeight bsp
      · refine ⟨hammingNorm bsp.2, ?_, ?_⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨bsp.2, ?_, rfl⟩
          simp [hz_ker, hz_not]
        · exact hammingNorm_snd_le_symWeight bsp
    · intro d hd
      rcases Finset.mem_union.1 hd with hd | hd
      · rcases Finset.mem_image.1 hd with ⟨z, hz, rfl⟩
        have hz_mem : z ∈ (LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace := by
          simpa using hz
        have hz_ker : z ∈ LinearMap.ker C.H₂.toLin' := hz_mem.1
        have hz_not : z ∉ C.H₁.rowSpace := by
          exact hz_mem.2
        refine ⟨symWeight ((0 : Fin n → ZMod 2), z), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨((0 : Fin n → ZMod 2), z), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable ((0 : Fin n → ZMod 2), z) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · simp [CSSPair.toBSM, sympForm_zero_fst]
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₂ z).1 hz_ker i₂
                simpa [CSSPair.toBSM, sympForm_zero_snd] using this
            · intro hrow
              exact hz_not ((cssBSM_rowSpace_iff C.H₁ C.H₂ 0 z).1 hrow).2
          simpa [BinSympMatrix.undetectableSet] using hbsp
        · exact (symWeight_zero_fst z).le
      · rcases Finset.mem_image.1 hd with ⟨x, hx, rfl⟩
        have hx_mem : x ∈ (LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace := by
          simpa using hx
        have hx_ker : x ∈ LinearMap.ker C.H₁.toLin' := hx_mem.1
        have hx_not : x ∉ C.H₂.rowSpace := by
          exact hx_mem.2
        refine ⟨symWeight (x, (0 : Fin n → ZMod 2)), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨(x, (0 : Fin n → ZMod 2)), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable (x, (0 : Fin n → ZMod 2)) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₁ x).1 hx_ker i₁
                simpa [CSSPair.toBSM, sympForm_zero_fst] using this
              · simp [CSSPair.toBSM, sympForm_zero_snd]
            · intro hrow
              exact hx_not ((cssBSM_rowSpace_iff C.H₁ C.H₂ x 0).1 hrow).1
          simpa [BinSympMatrix.undetectableSet] using hbsp
        · exact (symWeight_zero_snd x).le
  have hx_bound : ∀ d ∈ xWeights, d ≤ n := by
    intro d hd
    rcases Finset.mem_image.1 hd with ⟨z, _, rfl⟩
    simpa using (hammingNorm_le_card_fintype (x := z))
  have hz_bound : ∀ d ∈ zWeights, d ≤ n := by
    intro d hd
    rcases Finset.mem_image.1 hd with ⟨x, _, rfl⟩
    simpa using (hammingNorm_le_card_fintype (x := x))
  have hdist :
      C.toBSM.distance (Nat.add_pos_left C.nt₁ _) =
        (match bsmWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    rfl
  have hdx :
      C.dX =
        (match xWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    unfold CSSPair.dX minWeightKerNotMemRowspace
    rfl
  have hdz :
      C.dZ =
        (match zWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    unfold CSSPair.dZ minWeightKerNotMemRowspace
    rfl
  rw [hdist, hdx, hdz, hbsm_min]
  exact min_with_fallback_union_eq_min hx_bound hz_bound

/-- A CSS distance of at most `n` means some error really is undetectable. -/
theorem CSS.toBSM_undetectableSet_nonempty (C : CSSPair n k₁ k₂)
    (h_dist : min C.dX C.dZ ≤ n) : C.toBSM.undetectableSet.Nonempty := by
  exact BinSympMatrix.undetectableSet_nonempty C.toBSM (Nat.add_pos_left C.nt₁ _) (by
    rwa [CSS.toBSM_dist_eq])

/-- Orthogonal generators span codes that are dual to one another. -/
lemma toCodeSpace_subset_dual_of_orth_gen {n k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h_orth : M₁.mutuallyOrthRows M₂) :
    (M₁.toCodeSpace : Set (Fin n → ZMod 2)) ⊆ M₂.toCodeSpace.dualCode := by
  show (M₁.rowSpace : Set (Fin n → ZMod 2)) ⊆ CodeSpace.dualCode M₂.rowSpace
  refine Submodule.span_le.2 ?_
  rintro y ⟨i, rfl⟩
  show M₁ i ∈ M₂.rowSpace.orthogonalBilin (dotProductBilin _ _)
  rw [Submodule.mem_orthogonalBilin_iff]
  intro z hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨j, rfl⟩
    rw [dotProductBilin_apply_apply, dotProduct_comm]
    exact h_orth i j
  · simp
  · intro a b _ _ ha hb
    rw [dotProductBilin_apply_apply] at ha hb ⊢
    rw [add_dotProduct, ha, hb, zero_add]
  · intro a b _ hb
    rw [dotProductBilin_apply_apply] at hb ⊢
    rw [smul_dotProduct, hb, smul_zero]

/-- Two mutually orthogonal check matrices form a CSS code, the classical codes being the duals of
the spans of their rows. -/
def CSSPair.ofMatrices [NeZero k₁] [NeZero k₂] (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h_orth : H₁.mutuallyOrthRows H₂) :
    CSSPair n k₁ k₂ where
  C₁ := H₁.toCodeSpace.dualCode
  C₂ := H₂.toCodeSpace.dualCode
  H_dual := by
    rw [dual_dual_eq]
    apply toCodeSpace_subset_dual_of_orth_gen _ _ h_orth
  H₁ := H₁
  H₂ := H₂
  hpc₁ := by
    unfold CodeSpace.parityCheckedBy
    rw [dual_dual_eq]
    apply CodeSpace.toCodeSpace_spannedBy
  hpc₂ := by
    unfold CodeSpace.parityCheckedBy
    rw [dual_dual_eq]
    apply CodeSpace.toCodeSpace_spannedBy
  nt₁ := NeZero.pos _
  nt₂ := NeZero.pos _

noncomputable section

variable {n : ℕ}

/-- Orthogonal check matrices give commuting checks. -/
lemma cssBSM_isCommuting {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutuallyOrthRows H₂) :
    (cssBSM H₁ H₂).isCommuting := by
  have h₁₂ : ∀ x y, H₁ x ⬝ᵥ H₂ y = 0 := h
  have h₂₁ : ∀ x y, H₂ x ⬝ᵥ H₁ y = 0 := fun x y => (dotProduct_comm _ _).trans (h y x)
  intro r₁ r₂
  refine Fin.addCases (fun x => ?_) (fun x => ?_) r₁ <;>
    refine Fin.addCases (fun y => ?_) (fun y => ?_) r₂ <;>
    simp [BinSympMatrix.rowProd, sympForm_zero_fst, sympForm_zero_snd, h₁₂, h₂₁]

/-- The row space has dimension the rank. -/
lemma _root_.Matrix.finrank_rowSpace_eq_rank {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) M.rowSpace = M.rank := by
  rw [Matrix.rowSpace, Matrix.rank_eq_finrank_span_row]

/-- Rank–nullity, for a matrix presented together with a spanning set of its kernel. -/
lemma _root_.Matrix.rank_add_rank_ker {k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : M₂.isKerFor M₁) :
    M₁.rank + M₂.rank = n := by
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' M₁)) = M₂.rank := by
    rw [← h, Matrix.finrank_rowSpace_eq_rank]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M₁)
  rw [show Matrix.mulVecLin M₁ = Matrix.toLin' M₁ from rfl, hker] at hrn
  rw [show M₁.rank = Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' M₁)) from rfl]
  simpa using hrn

/-- The dimension of a product of subspaces is the sum of the dimensions. -/
lemma finrank_submodule_prod {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) V] [Module.Finite (ZMod 2) W]
    (p : Submodule (ZMod 2) V) (q : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) (p.prod q)
      = Module.finrank (ZMod 2) p + Module.finrank (ZMod 2) q := by
  have e : (p.prod q) ≃ₗ[ZMod 2] (p × q) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
      invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [e.finrank_eq, Module.finrank_prod]

/-- The row space of a CSS check matrix splits as a product of the two classical row spaces. -/
lemma cssBSM_rowSpace_eq {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    (cssBSM H₁ H₂).rowSpace = (H₂.rowSpace).prod (H₁.rowSpace) := by
  apply le_antisymm
  · rw [BinSympMatrix.rowSpace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [cssBSM_row_castAdd]
      exact ⟨Submodule.zero_mem _, Matrix.row_mem_rowSpace⟩
    · rw [cssBSM_row_natAdd]
      exact ⟨Matrix.row_mem_rowSpace, Submodule.zero_mem _⟩
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hx_pair : ((x, 0) : SympSpace n) ∈ (cssBSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => ((y, 0) : SympSpace n) ∈ (cssBSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.natAdd k₁ j, ?_⟩
        simp [Matrix.row_apply']
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem _ ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem _ a hy
    have hz_pair : ((0, z) : SympSpace n) ∈ (cssBSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => ((0, y) : SympSpace n) ∈ (cssBSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.castAdd k₂ j, ?_⟩
        simp [Matrix.row_apply']
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem _ ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem _ a hy
    simpa [Prod.ext_iff] using Submodule.add_mem _ hx_pair hz_pair

/-- The number of independent checks decomposes over the two classical check matrices. -/
theorem cssBSM_finrank_rowSpace {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) (cssBSM H₁ H₂).rowSpace = H₂.rank + H₁.rank := by
  rw [cssBSM_rowSpace_eq, finrank_submodule_prod, Matrix.finrank_rowSpace_eq_rank,
    Matrix.finrank_rowSpace_eq_rank]

/-- A pair of mutually orthogonal classical check matrices gives an `⟦n, k, d⟧` stabilizer code. -/
theorem cssIsCode {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutuallyOrthRows H₂) (hk : 0 < k₁ + k₂)
    (k d : ℕ) (hgen : k = n - (H₂.rank + H₁.rank)) (hkpos : 0 < k)
    (hd : d ≤ (cssBSM H₁ H₂).distance hk) :
    (cssBSM H₁ H₂).IsCode k d :=
  (cssBSM H₁ H₂).isCode_of (cssBSM_isCommuting H₁ H₂ h) hk
    (by rw [cssBSM_finrank_rowSpace, hgen]) hkpos hd

/-- The two check matrices of a CSS code are mutually orthogonal. -/
lemma CSSPair.orth (C : CSSPair n k₁ k₂) : C.H₁.mutuallyOrthRows C.H₂ := by
  intro x y
  have hy := C.C₂.pcb_prod_mem_dual y C.hpc₂
  have hx : C.H₁ x ∈ C.C₂ := C.H_dual (C.C₁.pcb_prod_mem_dual x C.hpc₁)
  unfold CodeSpace.dualCode at hy
  rw [Submodule.mem_orthogonalBilin_iff] at hy
  exact hy _ hx

/-- A CSS code with `k` logical qubits and distance at least `d` is an `⟦n, k, d⟧` code. -/
theorem CSSPair.isCode (C : CSSPair n k₁ k₂) (k d : ℕ)
    (hgen : k = n - (C.H₂.rank + C.H₁.rank)) (hkpos : 0 < k)
    (hd : d ≤ C.toBSM.distance (Nat.add_pos_left C.nt₁ k₂)) :
    C.toBSM.IsCode k d :=
  cssIsCode C.H₁ C.H₂ C.orth (Nat.add_pos_left C.nt₁ k₂) k d hgen hkpos hd

end

end QuantumLib
