import LeanQEC.LinearAlgebra.RowspaceKernel

open Finset

lemma weight_ge_of_cuts {n m : ℕ} (x : Fin n → ZMod 2) (S : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hodd : ∀ i, ∑ q ∈ S i, x q = 1) :
    m ≤ hammingNorm x := by
  classical
  have hsupp : ∀ i, ∃ q ∈ S i, x q ≠ 0 := by
    intro i
    by_contra h
    push_neg at h
    have h0 : ∑ q ∈ S i, x q = 0 := Finset.sum_eq_zero (fun q hq => h q hq)
    rw [hodd i] at h0
    exact one_ne_zero h0
  choose f hf hfne using hsupp
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hd := hdisj i j hne
    have hi : f i ∈ S i := hf i
    have hj : f j ∈ S j := hf j
    rw [hij] at hi
    exact (Finset.disjoint_left.mp hd) hi (hij ▸ hj)
  have hsub : Finset.image f Finset.univ ⊆ Finset.univ.filter (fun q => x q ≠ 0) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨i, _, rfl⟩ := hq
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hfne i⟩
  have hcard : (Finset.image f Finset.univ).card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnorm : hammingNorm x = (Finset.univ.filter (fun q => x q ≠ 0)).card := by
    simp [hammingNorm]
  rw [hnorm, ← hcard]
  exact Finset.card_le_card hsub

lemma MWK_ge {n k₁ k₂ : ℕ} (M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
    (M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)) (d : ℕ) (hd : d ≤ n + 1)
    (H : ∀ x, x ∈ LinearMap.ker M₁.toLin' → x ∉ M₂.rowSpace → d ≤ hammingNorm x) :
    d ≤ min_weight_ker_not_mem_rowspace M₁ M₂ := by
  unfold min_weight_ker_not_mem_rowspace
  extract_lets ue
  rcases hmin : (Finset.image hammingNorm ue.toFinset).min with _ | a
  · simpa using hd
  · simp only
    have hmem := Finset.mem_of_min hmin
    rw [Finset.mem_image] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hy' : y ∈ ue := Set.mem_toFinset.mp hy
    have hy'' : y ∈ (LinearMap.ker M₁.toLin' : Set _) \ (M₂.rowSpace : Set _) := hy'
    rw [Set.mem_diff] at hy''
    exact H y hy''.1 hy''.2
