import LeanQEC.Unitary.Basic
import LeanQEC.States.Phase

lemma matrix_cast {t₁ t₁' t₂ t₂'}
  (eq_t₁ : t₁ = t₁') (eq_t₂ : t₂ = t₂') :
  Matrix t₁ t₂ ℂ = Matrix t₁' t₂' ℂ := by
  rw [eq_t₁, eq_t₂]


lemma matrix_entry_of_cast {t₁ t₁' t₂ t₂'}
  (eq_t₁ : t₁ = t₁') (eq_t₂ : t₂ = t₂')
  (i : t₁) (j : t₂) (M : Matrix t₁' t₂' ℂ) :
  M (cast eq_t₁ i) (cast eq_t₂ j) =
  (cast (matrix_cast eq_t₁ eq_t₂).symm M) i j := by
  subst eq_t₁
  subst eq_t₂
  simp

lemma unitary_cast {n n'} (eq_n : n = n') :
  ↥𝐔ₙ[n] = ↥𝐔ₙ[n'] := by aesop

lemma bitvec_matrix_cast {n n'} (eq_n : n = n') :
  Matrix (BitVec n) (BitVec n) ℂ =
  Matrix (BitVec n') (BitVec n') ℂ := by aesop

lemma unitary_cast_coe {n n'} (eq_n : n = n') (U : ↥𝐔ₙ[n]) :
  ((cast (unitary_cast eq_n) U).1) = cast (bitvec_matrix_cast eq_n) (U.1) := by
  aesop

lemma eq_bitvec_assoc {n₁ n₂ n₃} :
  BitVec (n₁ + n₂ + n₃) = BitVec (n₁ + (n₂ + n₃)) := by
  rw [add_assoc]

lemma cast_to_bvcast {n n'} (eq_n : n = n') (s : BitVec n):
  cast (by rw [eq_n]) s = BitVec.cast eq_n s := by
  aesop

lemma bits_split_eq1 {n₁ n₂ n₃} (s : BitVec (n₁ + n₂ + n₃)) :
  (bits_cat.symm (bits_cat.symm s).1).1 =
  (bits_cat.symm (cast eq_bitvec_assoc s)).1 := by
  ext i H
  simp [bits_cat]
  rw [cast_to_bvcast]
  swap; rw [add_assoc]
  simp

lemma bits_split_eq2 {n₁ n₂ n₃} (s : BitVec (n₁ + n₂ + n₃)) :
  (bits_cat.symm (bits_cat.symm s).1).2 =
  (bits_cat.symm (bits_cat.symm (cast eq_bitvec_assoc s)).2).1 := by
  ext i H
  simp [bits_cat]
  rw [cast_to_bvcast]
  swap; rw [add_assoc]
  simp
  suffices: (i < n₂ + n₃)
  · aesop
  have hb : n₂ ≤ n₂ + n₃ := Nat.le_add_right n₂ n₃
  exact lt_of_lt_of_le H hb

lemma bits_split_eq3 {n₁ n₂ n₃} (s : BitVec (n₁ + n₂ + n₃)) :
  (bits_cat.symm s).2 =
  (bits_cat.symm (bits_cat.symm (cast eq_bitvec_assoc s)).2).2 := by
  ext i H
  simp [bits_cat]
  rw [cast_to_bvcast]
  swap; rw [add_assoc]
  simp_all
  suffices: n₁ + n₂ + i = n₁ + (n₂ + i)
  · aesop
  rw [add_assoc]

-- ??????
-- don't ask...
lemma kron_assoc {n₁ n₂ n₃} (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) (U₃ : 𝐔ₙ[n₃]) :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ ≍ (U₁ ⊗ₙ (U₂ ⊗ₙ U₃)) := by
  apply heq_of_eq_cast
  swap
  · suffices: n₁ + (n₂ + n₃) = n₁ + n₂ + n₃
    · rw [this]
    group
  apply unitary_ext
  apply Matrix.ext; intros i j
  let i₁ := (bits_cat.symm (bits_cat.symm i).1).1
  let i₂ := (bits_cat.symm (bits_cat.symm i).1).2
  let i₃ := (bits_cat.symm i).2
  let j₁ := (bits_cat.symm (bits_cat.symm j).1).1
  let j₂ := (bits_cat.symm (bits_cat.symm j).1).2
  let j₃ := (bits_cat.symm j).2
  simp [unitary_nkron, normalized_kron]
  conv =>
    enter[1]
    change U₁ i₁ j₁ * U₂ i₂ j₂ * U₃ i₃ j₃
  rw [unitary_cast_coe]
  rw [<- matrix_entry_of_cast]
  rotate_left
  · rw [add_assoc]
  · rw [add_assoc]
  · rw [add_assoc]
  simp
  rw [mul_assoc]
  congr
  · rw [<- bits_split_eq1]
    rw [<- bits_split_eq1]
  · rw [<- bits_split_eq2]
    rw [<- bits_split_eq2]
  · rw [<- bits_split_eq3]
    rw [<- bits_split_eq3]

lemma unitary_nkron_zero_id_left {n : ℕ} (U : 𝐔ₙ[n]) : unitary_nkron (1 : 𝐔ₙ[0]) U ≍ U := by
  apply heq_of_eq_cast
  swap
  rw [zero_add]
  apply unitary_ext
  ext i j
  simp [unitary_nkron, normalized_kron, unitary_cast_coe, <- matrix_entry_of_cast]
  simp [bits_cat]
  have h_1 : (1 : (Matrix (BitVec 0) (BitVec 0) ℂ)) (bits_cat.symm i).1 (bits_cat.symm j).1 = 1
  · show (((OfNat.ofNat 1) : Matrix (BitVec 0) (BitVec 0) ℂ)
    (bits_cat.invFun i).1 (bits_cat.invFun j).1 = 1)
    unfold bits_cat
    simp only [BitVec.extractLsb'_eq_zero, Matrix.one_apply_eq]
  rw [h_1, one_mul]
  congr! --just congr doesn't work, couldn't possibly imagine why
  all_goals --??????
    ext x i h
    rw [cast_to_bvcast]
    swap
    rw [zero_add]
    simp only [BitVec.getElem_extractLsb', zero_add, BitVec.getElem_cast]
    rfl

--much easier because defeq, typechecks
lemma unitary_nkron_zero_id_right {n : ℕ} (U : 𝐔ₙ[n]) : unitary_nkron U (1 : 𝐔ₙ[0]) = U := by
  apply unitary_ext
  ext i j
  simp [unitary_nkron, normalized_kron, normalize_mat, bits_cat]

/-This can be stated, general form cannot due to typechecking reasons. Found in Unitary.KronAssoc.lean -/
lemma unitary1_kron_assoc {U₁ U₂ U₃ : 𝐔ₙ[1]}  :
  (U₁ ⊗ₙ U₂) ⊗ₙ U₃ = U₁ ⊗ₙ (U₂ ⊗ₙ U₃) := by
  ext i j;
  simp [ unitary_nkron, normalized_kron ];
  ring_nf
  fin_cases i <;> fin_cases j <;> rfl


@[simp]
lemma zero_tensor_one_id {U : 𝐔ₙ[1]} : (1 : 𝐔ₙ[0]) ⊗ₙ U = U := by
  rw [←heq_iff_eq]
  exact (unitary_nkron_zero_id_left _)
