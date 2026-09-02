import Mathlib
import LeanQEC.Stabilizer.Basic
import LeanQEC.Classical_EC.Basic

variable {n k₁ k₂ : ℕ}

def CSS_BSM (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) : BinSympMatrix (k₁ + k₂) n where
    X := Fin.append (fun (_ : Fin k₁) => (fun _ => 0)) H₂
    Z := Fin.append H₁ (fun (_ : Fin k₂) => (fun _ => 0))

theorem CSS_BSM_is_comm {C₁ C₂ : CodeSpace n} (H_dual : (C₁.dualCode : Set (Fin n → ZMod 2)) ⊆ C₂) {H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)} (hpc₁ : C₁.parity_checked_by H₁)
  (hpc₂ : C₂.parity_checked_by H₂) : (CSS_BSM H₁ H₂).isCommuting := by
  intros r₁ r₂
  unfold CSS_BSM BinSympMatrix.rowProd symplecticProd
  have h : ∀ x y, H₁ x ⬝ᵥ H₂ y = 0 := by
    intros x y
    have hy := C₂.pcb_prod_mem_dual y hpc₂
    have hx : H₁ x ∈ C₂ := by
      apply H_dual
      apply C₁.pcb_prod_mem_dual x hpc₁
    unfold CodeSpace.dualCode at hy
    rw [Submodule.mem_orthogonalBilin_iff] at hy
    apply hy _ hx
  refine Fin.addCases (fun x => ?_) (fun x => ?_) r₁ <;>
  refine Fin.addCases (fun y => ?_) (fun y => ?_) r₂ <;>
  simp [Fin.append, BinSympMatrix.row]
  · apply h x y
  rw [dotProduct_comm]
  apply h y x

structure CSS_pair (n k₁ k₂) where
  C₁ : CodeSpace n
  C₂ : CodeSpace n
  H_dual : (C₁.dualCode : Set (Fin n → ZMod 2)) ⊆ C₂
  H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)
  H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)
  hpc₁ : C₁.parity_checked_by H₁
  hpc₂ : C₂.parity_checked_by H₂
  nt₁ : 0 < k₁
  nt₂ : 0 < k₂


def CSS_pair.toBSM (C : CSS_pair n k₁ k₂) := CSS_BSM C.H₁ C.H₂

noncomputable def CSS_pair.dX (C : CSS_pair n k₁ k₂) := min_weight_ker_not_mem_rowspace C.H₂ C.H₁

noncomputable def CSS_pair.dZ (C : CSS_pair n k₁ k₂) := min_weight_ker_not_mem_rowspace C.H₁ C.H₂

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
          simp

private lemma CSS_BSM_rowSpace_iff
    (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
    (x z : Fin n → ZMod 2) :
    (x, z) ∈ (CSS_BSM H₁ H₂).rowSpace ↔
      x ∈ H₂.rowSpace ∧ z ∈ H₁.rowSpace := by
  constructor
  · intro h
    let prodRows : Submodule (ZMod 2) (BinSympPauli n) :=
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
    have hle : (CSS_BSM H₁ H₂).rowSpace ≤ prodRows := by
      apply Submodule.span_le.2
      rintro _ ⟨i, rfl⟩
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · constructor
        · change (Fin.append (fun (_ : Fin k₁) => (fun _ => 0)) H₂ (Fin.castAdd k₂ i₁)) ∈ H₂.rowSpace
          rw [Fin.append_left]
          exact Submodule.zero_mem _
        · simpa [CSS_BSM, BinSympMatrix.row, Matrix.row] using
            (Matrix.row_mem_rowSpace (M := H₁) (i := i₁))
      · constructor
        · simpa [CSS_BSM, BinSympMatrix.row, Matrix.row] using
            (Matrix.row_mem_rowSpace (M := H₂) (i := i₂))
        · change (Fin.append H₁ (fun (_ : Fin k₂) => (fun _ => 0)) (Fin.natAdd k₁ i₂)) ∈ H₁.rowSpace
          rw [Fin.append_right]
          exact Submodule.zero_mem _
    exact hle h
  · rintro ⟨hx, hz⟩
    have hx_pair : (x, 0) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (y, 0) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.natAdd k₁ i, ?_⟩
        ext j <;> simp [CSS_BSM, BinSympMatrix.row]
      · exact Submodule.zero_mem ((CSS_BSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((CSS_BSM H₁ H₂).rowSpace) a hy
    have hz_pair : (0, z) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => (0, y) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨i, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.castAdd k₂ i, ?_⟩
        ext j <;> simp [CSS_BSM, BinSympMatrix.row]
      · exact Submodule.zero_mem ((CSS_BSM H₁ H₂).rowSpace)
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem ((CSS_BSM H₁ H₂).rowSpace) a hy
    simpa [Prod.ext_iff] using
      Submodule.add_mem ((CSS_BSM H₁ H₂).rowSpace) hx_pair hz_pair

private lemma zmod2_or_val_ge_left (a b : ZMod 2) : a.1 ≤ (ZMod2_or a b).1 := by
  native_decide +revert

private lemma zmod2_or_val_ge_right (a b : ZMod 2) : b.1 ≤ (ZMod2_or a b).1 := by
  native_decide +revert

private lemma hammingNorm_le_union_weight_left'
    (v₁ v₂ : Fin n → ZMod 2) :
    hammingNorm v₁ ≤ union_weight v₁ v₂ := by
  let v : Fin n → ZMod 2 := fun i => ZMod2_or (v₁ i) (v₂ i)
  have hv_eq : hammingNorm v = ∑ i, (v i).1 := by
    refine le_antisymm
      ((weight_le_disj (z := v) (k := ∑ i, (v i).1)).2 le_rfl)
      ((weight_le_disj (z := v) (k := hammingNorm v)).1 le_rfl)
  rw [weight_le_disj]
  rw [show union_weight v₁ v₂ = hammingNorm v by rfl, hv_eq]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact zmod2_or_val_ge_left (v₁ i) (v₂ i)

private lemma hammingNorm_le_union_weight_right'
    (v₁ v₂ : Fin n → ZMod 2) :
    hammingNorm v₂ ≤ union_weight v₁ v₂ := by
  let v : Fin n → ZMod 2 := fun i => ZMod2_or (v₁ i) (v₂ i)
  have hv_eq : hammingNorm v = ∑ i, (v i).1 := by
    refine le_antisymm
      ((weight_le_disj (z := v) (k := ∑ i, (v i).1)).2 le_rfl)
      ((weight_le_disj (z := v) (k := hammingNorm v)).1 le_rfl)
  rw [weight_le_disj]
  rw [show union_weight v₁ v₂ = hammingNorm v by rfl, hv_eq]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact zmod2_or_val_ge_right (v₁ i) (v₂ i)

set_option maxHeartbeats 0 in
theorem CSS.toBSM_dist_eq (C : CSS_pair n k₁ k₂) :
  C.toBSM.distance (Nat.add_pos_left C.nt₁ _) = min C.dX C.dZ := by
  let xWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace).toFinset)
  let zWeights : Finset ℕ :=
    Finset.image hammingNorm
      (((LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace).toFinset)
  let bsmWeights : Finset ℕ :=
    Finset.image BinSympPauli.weight C.toBSM.undetectable_set
  have hbsm_min : bsmWeights.min = (xWeights ∪ zWeights).min := by
    apply finset_min_eq_of_forall_exists_le
    · intro d hd
      rcases Finset.mem_image.1 hd with ⟨bsp, hbsp, rfl⟩
      have hbsp' : C.toBSM.undetectable bsp := by
        simpa [BinSympMatrix.undetectable_set] using hbsp
      rcases hbsp' with ⟨hcomm, hnot_row⟩
      have hx_ker : bsp.1 ∈ LinearMap.ker C.H₁.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.castAdd k₂ i)
        simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd, Matrix.row] using this
      have hz_ker : bsp.2 ∈ LinearMap.ker C.H₂.toLin' := by
        rw [mem_ker_iff_dotProd_rows_eq_zero]
        intro i
        have := hcomm (Fin.natAdd k₁ i)
        simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd, Matrix.row] using this
      have hnot_or : bsp.1 ∉ C.H₂.rowSpace ∨ bsp.2 ∉ C.H₁.rowSpace := by
        by_contra h
        simp only [not_or, not_not] at h
        apply hnot_row
        exact (CSS_BSM_rowSpace_iff C.H₁ C.H₂ bsp.1 bsp.2).2 ⟨h.1, h.2⟩
      rcases hnot_or with hx_not | hz_not
      · refine ⟨hammingNorm bsp.1, ?_, ?_⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨bsp.1, ?_, rfl⟩
          simp [hx_ker, hx_not]
        · simpa [BinSympPauli.weight] using hammingNorm_le_union_weight_left' bsp.1 bsp.2
      · refine ⟨hammingNorm bsp.2, ?_, ?_⟩
        · apply Finset.mem_union_left
          rw [Finset.mem_image]
          refine ⟨bsp.2, ?_, rfl⟩
          simp [hz_ker, hz_not]
        · simpa [BinSympPauli.weight] using hammingNorm_le_union_weight_right' bsp.1 bsp.2
    · intro d hd
      rcases Finset.mem_union.1 hd with hd | hd
      · rcases Finset.mem_image.1 hd with ⟨z, hz, rfl⟩
        have hz_mem : z ∈ (LinearMap.ker C.H₂.toLin' : Set (Fin n → ZMod 2)) \ C.H₁.rowSpace := by
          simpa using hz
        have hz_ker : z ∈ LinearMap.ker C.H₂.toLin' := hz_mem.1
        have hz_not : z ∉ C.H₁.rowSpace := by
          exact hz_mem.2
        refine ⟨BinSympPauli.weight ((0 : Fin n → ZMod 2), z), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨((0 : Fin n → ZMod 2), z), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable ((0 : Fin n → ZMod 2), z) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · simp [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd]
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₂ z).1 hz_ker i₂
                simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd] using this
            · intro hrow
              exact hz_not ((CSS_BSM_rowSpace_iff C.H₁ C.H₂ 0 z).1 hrow).2
          simpa [BinSympMatrix.undetectable_set] using hbsp
        · simp [BinSympPauli.weight]
      · rcases Finset.mem_image.1 hd with ⟨x, hx, rfl⟩
        have hx_mem : x ∈ (LinearMap.ker C.H₁.toLin' : Set (Fin n → ZMod 2)) \ C.H₂.rowSpace := by
          simpa using hx
        have hx_ker : x ∈ LinearMap.ker C.H₁.toLin' := hx_mem.1
        have hx_not : x ∉ C.H₂.rowSpace := by
          exact hx_mem.2
        refine ⟨BinSympPauli.weight (x, (0 : Fin n → ZMod 2)), ?_, ?_⟩
        · rw [Finset.mem_image]
          refine ⟨(x, (0 : Fin n → ZMod 2)), ?_, rfl⟩
          have hbsp : C.toBSM.undetectable (x, (0 : Fin n → ZMod 2)) := by
            constructor
            · intro i
              refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
              · have := (mem_ker_iff_dotProd_rows_eq_zero C.H₁ x).1 hx_ker i₁
                simpa [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd] using this
              · simp [CSS_pair.toBSM, CSS_BSM, BinSympMatrix.row, symplecticProd]
            · intro hrow
              exact hx_not ((CSS_BSM_rowSpace_iff C.H₁ C.H₂ x 0).1 hrow).1
          simpa [BinSympMatrix.undetectable_set] using hbsp
        · simp [BinSympPauli.weight]
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
    unfold CSS_pair.dX min_weight_ker_not_mem_rowspace
    rfl
  have hdz :
      C.dZ =
        (match zWeights.min with
          | ⊤ => n + 1
          | some d => d) := by
    unfold CSS_pair.dZ min_weight_ker_not_mem_rowspace
    rfl
  rw [hdist, hdx, hdz, hbsm_min]
  exact min_with_fallback_union_eq_min hx_bound hz_bound

theorem CSS.toBSM_undetectable_set_nonempty (C : CSS_pair n k₁ k₂)
    (h_dist : min C.dX C.dZ ≤ n) : C.toBSM.undetectable_set.Nonempty := by
  exact BinSympMatrix.undetectable_set_nonempty C.toBSM (Nat.add_pos_left C.nt₁ _) (by
    rwa [CSS.toBSM_dist_eq])

lemma toCodeSpace_subset_dual_of_orth_gen {n k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h_orth : M₁.mutually_orth_rows M₂) :
  (M₁.toCodeSpace : Set (Fin n → ZMod 2)) ⊆ M₂.toCodeSpace.dualCode := by
  have htoRow₁ : M₁.toCodeSpace = M₁.rowSpace := by
      ext x
      simp [Matrix.toCodeSpace, Matrix.rowSpace]
  have htoRow₂ : M₂.toCodeSpace = M₂.rowSpace := by
    ext x
    simp [Matrix.toCodeSpace, Matrix.rowSpace]
  intro x hx
  rw [htoRow₁] at hx
  rw [htoRow₂]
  have hsubset : M₁.rowSpace ≤ CodeSpace.dualCode M₂.rowSpace := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨i, rfl⟩
    show M₁ i ∈ M₂.rowSpace.orthogonalBilin (dotProductBilin _ _)
    rw [Submodule.mem_orthogonalBilin_iff]
    intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨j, rfl⟩
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply, dotProduct_comm]
      exact h_orth i j
    · simp [LinearMap.IsOrtho]
    · intro a b _ _ ha hb
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply] at ha hb ⊢
      rw [add_dotProduct, ha, hb, zero_add]
    · intro a b _ hb
      rw [LinearMap.IsOrtho, dotProductBilin_apply_apply] at hb ⊢
      rw [smul_dotProduct, hb, smul_zero]
  exact hsubset hx

def CSS_pair.of_matrices [NeZero k₁] [NeZero k₂] (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)) (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
(h_orth : H₁.mutually_orth_rows H₂) : CSS_pair n k₁ k₂ where
  C₁ := H₁.toCodeSpace.dualCode
  C₂ := H₂.toCodeSpace.dualCode
  H_dual := by
    rw [dual_dual_eq]
    apply toCodeSpace_subset_dual_of_orth_gen _ _ h_orth
  H₁ := H₁
  H₂ := H₂
  hpc₁ := by
    unfold CodeSpace.parity_checked_by
    rw [dual_dual_eq]
    apply CodeSpace.toCodeSpace_spanned_by
  hpc₂ := by
    unfold CodeSpace.parity_checked_by
    rw [dual_dual_eq]
    apply CodeSpace.toCodeSpace_spanned_by
  nt₁ := NeZero.pos _
  nt₂ := NeZero.pos _

noncomputable section

variable {n : ℕ}

lemma fold_pgroup_phases_one {n : ℕ} (f : Fin n → pgroup_phases) (h : ∀ i, f i = 1) :
    fold_pgroup_phases f = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fold_pgroup_phases, h 0, ih (Fin.tail f) (fun i => h _), one_mul]

lemma toPauli_mul_of_phase_one {n : ℕ} (a b : BinSympPauli n)
    (h : ∀ i, (mul_Pauli1 (Z2Z2_Pauli_equiv (a.1 i, a.2 i))
      (Z2Z2_Pauli_equiv (b.1 i, b.2 i))).1 = 1) :
    BinSympPauli_toPauli a * BinSympPauli_toPauli b = BinSympPauli_toPauli (a + b) := by
  set ma : Fin n → Pauli := fun i => Z2Z2_Pauli_equiv (a.1 i, a.2 i) with hma
  set mb : Fin n → Pauli := fun i => Z2Z2_Pauli_equiv (b.1 i, b.2 i) with hmb
  have hsa : foldPauli.symm (BinSympPauli_toPauli a : PauliGroup n) = (pgphase_1, ma) := by
    simp [BinSympPauli_toPauli, hma]
  have hsb : foldPauli.symm (BinSympPauli_toPauli b : PauliGroup n) = (pgphase_1, mb) := by
    simp [BinSympPauli_toPauli, hmb]
  have hmul :
      foldPauli.symm
          ((BinSympPauli_toPauli a * BinSympPauli_toPauli b : PauliGroup_group n) : PauliGroup n)
        = mul_factored_Paulis (pgphase_1, ma) (pgphase_1, mb) := by
    rw [← hsa, ← hsb]
    apply foldPauli.injective
    apply Subtype.ext
    simpa using
      (mul_factored_Paulis_correct (foldPauli.symm (BinSympPauli_toPauli a : PauliGroup n))
        (foldPauli.symm (BinSympPauli_toPauli b : PauliGroup n))).symm
  have hfact : mul_factored_Paulis (pgphase_1, ma) (pgphase_1, mb)
      = (pgphase_1, fun i => (mul_Pauli1 (ma i) (mb i)).2) := by
    unfold mul_factored_Paulis scale_factored_Pauli mul_Pauli1_tuples collect_phases
      pointwise_mul_Paulis
    simp only
    rw [fold_pgroup_phases_one _ h]
    simp
  have hpauli : (fun i => (mul_Pauli1 (ma i) (mb i)).2)
      = fun i => Z2Z2_Pauli_equiv ((a + b).1 i, (a + b).2 i) := by
    funext i
    have h2 := congrArg Z2Z2_Pauli_equiv (local_mul_Pauli_toBinSymp (ma i) (mb i))
    rw [Equiv.apply_symm_apply] at h2
    rw [h2, hma, hmb]
    simp [Equiv.symm_apply_apply]
  apply Subtype.ext
  have hval := congrArg (fun z => ((foldPauli z : PauliGroup n) : 𝐔ₙ[n])) hmul
  simp only [Equiv.apply_symm_apply] at hval
  rw [hval, hfact, hpauli]
  rfl

def xPauli {n : ℕ} (u : Fin n → ZMod 2) : PauliGroup_group n := BinSympPauli_toPauli (u, 0)

def zPauli {n : ℕ} (v : Fin n → ZMod 2) : PauliGroup_group n := BinSympPauli_toPauli (0, v)

@[simp]
lemma xPauli_zero : xPauli (0 : Fin n → ZMod 2) = 1 := BinSympPauli_toPauli_zero
@[simp]
lemma zPauli_zero : zPauli (0 : Fin n → ZMod 2) = 1 := BinSympPauli_toPauli_zero
@[simp]
lemma toBinSymp_xPauli (u : Fin n → ZMod 2) :
    Pauli_toBinSympPauli (xPauli u) = (u, 0) :=
  Pauli_toBinSympPauli_BinSympPauli_toPauli _
@[simp]
lemma toBinSymp_zPauli (v : Fin n → ZMod 2) :
    Pauli_toBinSympPauli (zPauli v) = (0, v) :=
  Pauli_toBinSympPauli_BinSympPauli_toPauli _

lemma xPauli_mul (u u' : Fin n → ZMod 2) : xPauli u * xPauli u' = xPauli (u + u') := by
  refine (toPauli_mul_of_phase_one (u, 0) (u', 0) ?_).trans ?_
  · intro i
    show (mul_Pauli1 (Z2Z2_Pauli_equiv (u i, 0)) (Z2Z2_Pauli_equiv (u' i, 0))).1 = 1
    generalize u i = x
    generalize u' i = y
    fin_cases x <;> fin_cases y <;> simp [Z2Z2_Pauli_equiv, mul_Pauli1]
  · rfl

lemma zPauli_mul (v v' : Fin n → ZMod 2) : zPauli v * zPauli v' = zPauli (v + v') := by
  refine (toPauli_mul_of_phase_one (0, v) (0, v') ?_).trans ?_
  · intro i
    show (mul_Pauli1 (Z2Z2_Pauli_equiv (0, v i)) (Z2Z2_Pauli_equiv (0, v' i))).1 = 1
    generalize v i = x
    generalize v' i = y
    fin_cases x <;> fin_cases y <;> simp [Z2Z2_Pauli_equiv, mul_Pauli1]
  · rfl

lemma zPauli_mul_xPauli_comm {u v : Fin n → ZMod 2} (h : v ⬝ᵥ u = 0) :
    zPauli v * xPauli u = xPauli u * zPauli v := by
  have hcomm : commute (BinSympPauli_toPauli ((0 : Fin n → ZMod 2), v))
      (BinSympPauli_toPauli (u, (0 : Fin n → ZMod 2))) := by
    apply commutes_of_sympProd_zero
    simp [symplecticProd, h]
  exact (commute_iff_commute _ _).1 hcomm

lemma negIdPauli_ne_one (n : ℕ) : negIdPauli n ≠ 1 := by
  intro h
  have h1 : (1 : PauliGroup_group n) = scalarPauli pgphase_1 := one_eq_scalarPauli_one
  rw [h1, negIdPauli, scalarPauli, scalarPauli] at h
  have := foldPauli.injective (Subtype.ext (congrArg Subtype.val h))
  have hph : pgphase_n1 = pgphase_1 := congrArg Prod.fst this
  have : ((-1 : ℂ)) = 1 := congrArg (fun z => (z : pgroup_phases).1.z) hph
  norm_num at this

variable {k₁ k₂ : ℕ}

lemma zmod2_vec_add_self (u : Fin n → ZMod 2) : u + u = 0 := by
  funext i
  show u i + u i = 0
  generalize u i = a
  fin_cases a <;> rfl

def cssPauliSubgroup (A B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (horth : ∀ u ∈ A, ∀ v ∈ B, u ⬝ᵥ v = 0) : Subgroup (PauliGroup_group n) where
  carrier := {P | ∃ u ∈ A, ∃ v ∈ B, P = xPauli u * zPauli v}
  one_mem' := ⟨0, A.zero_mem, 0, B.zero_mem, by simp⟩
  mul_mem' := by
    rintro P Q ⟨u, hu, v, hv, rfl⟩ ⟨u', hu', v', hv', rfl⟩
    refine ⟨u + u', A.add_mem hu hu', v + v', B.add_mem hv hv', ?_⟩
    have hswap : zPauli v * xPauli u' = xPauli u' * zPauli v := by
      refine zPauli_mul_xPauli_comm ?_
      rw [dotProduct_comm]
      exact horth u' hu' v hv
    calc xPauli u * zPauli v * (xPauli u' * zPauli v')
        = xPauli u * (zPauli v * xPauli u') * zPauli v' := by group
      _ = xPauli u * (xPauli u' * zPauli v) * zPauli v' := by rw [hswap]
      _ = (xPauli u * xPauli u') * (zPauli v * zPauli v') := by group
      _ = xPauli (u + u') * zPauli (v + v') := by rw [xPauli_mul, zPauli_mul]
  inv_mem' := by
    rintro P ⟨u, hu, v, hv, rfl⟩
    refine ⟨u, hu, v, hv, ?_⟩
    have hswap : zPauli v * xPauli u = xPauli u * zPauli v := by
      refine zPauli_mul_xPauli_comm ?_
      rw [dotProduct_comm]
      exact horth u hu v hv
    have hsq : (xPauli u * zPauli v) * (xPauli u * zPauli v) = 1 := by
      calc xPauli u * zPauli v * (xPauli u * zPauli v)
          = xPauli u * (zPauli v * xPauli u) * zPauli v := by group
        _ = xPauli u * (xPauli u * zPauli v) * zPauli v := by rw [hswap]
        _ = (xPauli u * xPauli u) * (zPauli v * zPauli v) := by group
        _ = xPauli (u + u) * zPauli (v + v) := by rw [xPauli_mul, zPauli_mul]
        _ = 1 := by rw [zmod2_vec_add_self u, zmod2_vec_add_self v]; simp
    exact (inv_eq_self_of_mul_self_eq_one hsq).symm ▸ rfl

@[simp]
lemma mem_cssPauliSubgroup {A B : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {horth : ∀ u ∈ A, ∀ v ∈ B, u ⬝ᵥ v = 0} (P : PauliGroup_group n) :
    P ∈ cssPauliSubgroup A B horth ↔ ∃ u ∈ A, ∃ v ∈ B, P = xPauli u * zPauli v := Iff.rfl

lemma negIdPauli_notMem_cssPauliSubgroup (A B : Submodule (ZMod 2) (Fin n → ZMod 2))
    (horth : ∀ u ∈ A, ∀ v ∈ B, u ⬝ᵥ v = 0) :
    negIdPauli n ∉ cssPauliSubgroup A B horth := by
  rintro ⟨u, _, v, _, hP⟩
  have himg : Pauli_toBinSympPauli (negIdPauli n) = (u, v) := by
    rw [hP, Pauli_to_BinSymp_correct, toBinSymp_xPauli, toBinSymp_zPauli]
    simp
  have hzero : Pauli_toBinSympPauli (negIdPauli n) = 0 := by
    have : negIdPauli n ∈ PauliGroup.phaseSubgroup n := by
      rw [PauliGroup.mem_phaseSubgroup_iff_scalar]
      exact ⟨pgphase_n1, rfl⟩
    simpa [PauliGroup.mem_phaseSubgroup_iff] using this
  rw [hzero] at himg
  have hu : u = 0 := (congrArg Prod.fst himg).symm
  have hv : v = 0 := (congrArg Prod.snd himg).symm
  rw [hu, hv] at hP
  simp at hP
  exact negIdPauli_ne_one n hP

lemma rowSpace_orth_of_mutually_orth {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) :
    ∀ u ∈ H₂.rowSpace, ∀ v ∈ H₁.rowSpace, u ⬝ᵥ v = 0 := by
  intro u hu
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨i, rfl⟩ v hv
    rw [dotProduct_comm]
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨j, rfl⟩
      exact h j i
    · simp
    · intro a b _ _ ha hb
      rw [add_dotProduct, ha, hb, add_zero]
    · intro a b _ hb
      rw [smul_dotProduct, hb, smul_zero]
  · intro v _
    simp
  · intro a b _ _ ha hb v hv
    rw [add_dotProduct, ha v hv, hb v hv, add_zero]
  · intro a b _ hb v hv
    rw [smul_dotProduct, hb v hv, smul_zero]

lemma CSS_BSM_isCommuting {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) :
    (CSS_BSM H₁ H₂).isCommuting := by
  intro r₁ r₂
  unfold CSS_BSM BinSympMatrix.rowProd symplecticProd
  refine Fin.addCases (fun x => ?_) (fun x => ?_) r₁ <;>
    refine Fin.addCases (fun y => ?_) (fun y => ?_) r₂ <;>
    simp [Fin.append, BinSympMatrix.row]
  · exact h x y
  · rw [dotProduct_comm]
    exact h y x

lemma CSS_BSM_stabClosure_le {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) :
    (CSS_BSM H₁ H₂).stabClosure (CSS_BSM_isCommuting H₁ H₂ h) ≤
      cssPauliSubgroup H₂.rowSpace H₁.rowSpace (rowSpace_orth_of_mutually_orth H₁ H₂ h) := by
  rw [BinSympMatrix.stabClosure, Subgroup.closure_le]
  rintro P hP
  simp only [BinSympMatrix.toStabSet, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_univ, true_and] at hP
  obtain ⟨i, rfl⟩ := hP
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine ⟨0, Submodule.zero_mem _, H₁ j, Matrix.row_mem_rowSpace, ?_⟩
    have hrow : (CSS_BSM H₁ H₂).row (Fin.castAdd k₂ j) = (0, H₁ j) := by
      simp [CSS_BSM, BinSympMatrix.row, Fin.append_left]
      rfl
    rw [hrow, xPauli_zero, one_mul, zPauli]
  · refine ⟨H₂ j, Matrix.row_mem_rowSpace, 0, Submodule.zero_mem _, ?_⟩
    have hrow : (CSS_BSM H₁ H₂).row (Fin.natAdd k₁ j) = (H₂ j, 0) := by
      simp [CSS_BSM, BinSympMatrix.row, Fin.append_right]
      rfl
    rw [hrow, zPauli_zero, mul_one, xPauli]

theorem CSS_BSM_h_minus {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) :
    negIdPauli n ∉ (CSS_BSM H₁ H₂).stabClosure (CSS_BSM_isCommuting H₁ H₂ h) := fun hmem =>
  negIdPauli_notMem_cssPauliSubgroup _ _ _ (CSS_BSM_stabClosure_le H₁ H₂ h hmem)

def cssStabCode {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) : StabCode n :=
  StabCode_of_BinSympMatrix (CSS_BSM H₁ H₂) (CSS_BSM_isCommuting H₁ H₂ h)
    (CSS_BSM_h_minus H₁ H₂ h)

lemma Matrix.finrank_rowSpace_eq_rank {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) :
    Module.finrank (ZMod 2) M.rowSpace = M.rank := by
  rw [Matrix.rowSpace, Matrix.rank_eq_finrank_span_row]
  rfl

lemma Matrix.rank_add_rank_ker {k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : M₂.is_ker_for M₁) :
    M₁.rank + M₂.rank = n := by
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (Matrix.toLin' M₁)) = M₂.rank := by
    rw [← h, Matrix.finrank_rowSpace_eq_rank]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M₁)
  rw [show Matrix.mulVecLin M₁ = Matrix.toLin' M₁ from rfl, hker] at hrn
  rw [show M₁.rank = Module.finrank (ZMod 2) (LinearMap.range (Matrix.toLin' M₁)) from rfl]
  simpa using hrn
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

lemma CSS_BSM_rowSpace_eq {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) :
    (CSS_BSM H₁ H₂).rowSpace = (H₂.rowSpace).prod (H₁.rowSpace) := by
  apply le_antisymm
  · rw [BinSympMatrix.rowSpace, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hrow : (CSS_BSM H₁ H₂).row (Fin.castAdd k₂ j) = (0, H₁ j) := by
        simp [CSS_BSM, BinSympMatrix.row, Fin.append_left]
        rfl
      rw [hrow]
      exact ⟨Submodule.zero_mem _, Matrix.row_mem_rowSpace⟩
    · have hrow : (CSS_BSM H₁ H₂).row (Fin.natAdd k₁ j) = (H₂ j, 0) := by
        simp [CSS_BSM, BinSympMatrix.row, Fin.append_right]
        rfl
      rw [hrow]
      exact ⟨Matrix.row_mem_rowSpace, Submodule.zero_mem _⟩
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hx_pair : ((x, 0) : BinSympPauli n) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => ((y, 0) : BinSympPauli n) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.natAdd k₁ j, ?_⟩
        simp [CSS_BSM, BinSympMatrix.row, Fin.append_right]
        rfl
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem _ ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem _ a hy
    have hz_pair : ((0, z) : BinSympPauli n) ∈ (CSS_BSM H₁ H₂).rowSpace := by
      refine Submodule.span_induction
        (p := fun y _ => ((0, y) : BinSympPauli n) ∈ (CSS_BSM H₁ H₂).rowSpace) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨Fin.castAdd k₂ j, ?_⟩
        simp [CSS_BSM, BinSympMatrix.row, Fin.append_left]
        rfl
      · exact Submodule.zero_mem _
      · intro a b _ _ ha hb
        simpa using Submodule.add_mem _ ha hb
      · intro a y _ hy
        simpa using Submodule.smul_mem _ a hy
    simpa [Prod.ext_iff] using Submodule.add_mem _ hx_pair hz_pair

/- Number of independent generators decomposes over the two check matrices -/
theorem cssStabCode_generators {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) :
    (cssStabCode H₁ H₂ h).numGenerators = H₂.rank + H₁.rank := by
  rw [cssStabCode, BinSympMatrix.numGenerators_eq_finrank_rowSpace, CSS_BSM_rowSpace_eq,
    finrank_submodule_prod, Matrix.finrank_rowSpace_eq_rank, Matrix.finrank_rowSpace_eq_rank]

/- Agreement -/
theorem cssStabCode_distance {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) (hk : 0 < k₁ + k₂) :
    (cssStabCode H₁ H₂ h).distance = (CSS_BSM H₁ H₂).distance hk :=
  BinSympMatrix.distance_eq_distance _ _ _ hk

theorem cssStabCode_param_triple {k₁ k₂ : ℕ} (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (h : H₁.mutually_orth_rows H₂) (hk : 0 < k₁ + k₂)
    (k d : ℕ) (hgen : k = n - (H₂.rank + H₁.rank))
    (hd : d ≤ (CSS_BSM H₁ H₂).distance hk) :
    param_triple (cssStabCode H₁ H₂ h) k d := by
  refine StabCode.param_triple_of _ k d ?_ ?_
  · rw [cssStabCode_generators, hgen]
  · rw [cssStabCode_distance H₁ H₂ h hk]
    exact hd

lemma CSS_pair.orth (C : CSS_pair n k₁ k₂) : C.H₁.mutually_orth_rows C.H₂ := by
  intro x y
  have hy := C.C₂.pcb_prod_mem_dual y C.hpc₂
  have hx : C.H₁ x ∈ C.C₂ := C.H_dual (C.C₁.pcb_prod_mem_dual x C.hpc₁)
  unfold CodeSpace.dualCode at hy
  rw [Submodule.mem_orthogonalBilin_iff] at hy
  exact hy _ hx

def CSS_pair.toStabCode (C : CSS_pair n k₁ k₂) : StabCode n :=
  cssStabCode C.H₁ C.H₂ C.orth

theorem CSS_pair.param_triple_of (C : CSS_pair n k₁ k₂) (k d : ℕ)
    (hgen : k = n - (C.H₂.rank + C.H₁.rank))
    (hd : d ≤ C.toBSM.distance (Nat.add_pos_left C.nt₁ k₂)) :
    param_triple C.toStabCode k d :=
  cssStabCode_param_triple C.H₁ C.H₂ C.orth (Nat.add_pos_left C.nt₁ k₂) k d hgen hd

end
