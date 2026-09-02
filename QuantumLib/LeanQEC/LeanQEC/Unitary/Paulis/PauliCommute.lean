import LeanQEC.Unitary.Paulis.PauliMul

noncomputable section

def neg_phase (c : phase) : phase where
  z := -c.z
  z_norm := by
    norm_num
    apply c.z_norm

instance : Neg phase where
  neg := neg_phase

lemma neg_phaseE (c : phase) :
  -c = neg_phase c := by rfl

def commute₁ (P P' : Pauli) := P = Pauli_I || P' = Pauli_I || P = P'

lemma mem_neg_pphase (c : pgroup_phases) :
  -c.val ∈ pgroup_phases := by
  have: -c.val = neg_phase c.val := by rfl
  rw [this]
  clear this
  simp [neg_phase]
  rcases (pgphase_cases c) with H | H | H | H
  all_goals simp [pgroup_phases, H]

def neg_pphase (c : pgroup_phases) : pgroup_phases :=
  ⟨-c.val, mem_neg_pphase c⟩

instance : Neg pgroup_phases where
  neg := neg_pphase

lemma neg_pgphaseE (c : pgroup_phases) :
  -c = neg_pphase c := by rfl

lemma commute₁_right (P Q : Pauli) :
  (mul_Pauli1 P Q).2 = (mul_Pauli1 Q P).2 := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases Q) with rfl | rfl | rfl | rfl
  all_goals simp [mul_Pauli1]


lemma commute₁_correct_true (P Q : Pauli)
  (commutePQ : commute₁ P Q):
  (mul_Pauli1 P Q).1 = (mul_Pauli1 Q P).1 := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases Q) with rfl | rfl | rfl | rfl
  all_goals simp [commute₁] at commutePQ
  all_goals try rfl
  all_goals simp [mul_Pauli1]


lemma commute₁_correct_false (P Q : Pauli)
  (commutePQ : commute₁ P Q = false):
  (mul_Pauli1 P Q).1 = -(mul_Pauli1 Q P).1 := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases Q) with rfl | rfl | rfl | rfl
  all_goals simp [commute₁] at commutePQ
  all_goals simp [mul_Pauli1]
  all_goals simp [pgphase_i, pgphase_ni]
  all_goals rw [neg_pgphaseE, neg_pphase]
  all_goals simp [neg_phaseE, neg_phase]

-- too weak, maybe useless
lemma commute₁_cases (P Q : Pauli) :
  (mul_Pauli1 P Q).1 = (mul_Pauli1 Q P).1 ∨
  (mul_Pauli1 P Q).1 = -(mul_Pauli1 Q P).1 := by
  by_cases H: commute₁ P Q
  · left
    apply commute₁_correct_true; assumption
  · right
    apply commute₁_correct_false
    simp_all [Bool.not_eq_true]

lemma commute₁_sym P P' :
  commute₁ P P' ↔ commute₁ P' P := by
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals rcases (Pauli_cases P') with rfl | rfl | rfl | rfl
  all_goals simp [commute₁]

lemma commute₁_xx P : commute₁ P P := by simp [commute₁]

def anticommuteₘ {n} (m m' : Fin n -> Pauli) :=
  match n with
  | 0 => false
  | _ + 1 =>
    (!commute₁ (m 0) (m' 0)) ^^ anticommuteₘ (Fin.tail m) (Fin.tail m')

--why is this in this file?
lemma mul_nkrons {n₁ n₂} (U₁ U₁' : 𝐔ₙ[n₁]) (U₂ U₂' : 𝐔ₙ[n₂]) :
  (U₁ ⊗ₙ U₂) * (U₁' ⊗ₙ U₂') =
  (U₁ * U₁') ⊗ₙ (U₂ * U₂') := by
  simp [unitary_nkron, normalized_kron]
  rw [Matrix.mul_kronecker_mul]

def anticommuteₘ_iter {n} (m m' : Fin (n + 1) -> Pauli) :
  anticommuteₘ (Fin.tail m) (Fin.tail m') =
  (anticommuteₘ m m' ^^ (!commute₁ (m 0) (m' 0))) := by
  simp [anticommuteₘ]
  by_cases H: commute₁ (m 0) (m' 0)
  all_goals by_cases H': anticommuteₘ (Fin.tail m) (Fin.tail m')
  all_goals aesop

lemma unitary_n_nkron_iter {n} (m : Fin (n + 1) -> 𝐔ₙ[1]) :
    unitary_n_nkron m =
    unitary_n_nkron (Fin.tail m) ⊗ₙ (m 0) := by
    rfl

def phase_n1 : phase := ⟨-1, by norm_num⟩

lemma neg_is_uphase {n} (U : 𝐔ₙ[n]) : -U = U_phase U phase_n1 := by
  simp [U_phase, phase_n1]; aesop

lemma uphase_of_kron_right {n₁ n₂} (z : phase) (m1 : 𝐔ₙ[n₁]) (m2 : 𝐔ₙ[n₂]) :
  m1 ⊗ₙ U_phase m2 z = U_phase (m1 ⊗ₙ m2) z := by
  apply unitary_ext
  simp [U_phase, unitary_nkron]
  simp [normalized_kron]
  simp [Matrix.kronecker_smul, Matrix.submatrix_smul]

lemma uphase_ext {n} (U U' : 𝐔ₙ[n]) c c' :
  U = U' ->
  c = c' ->
  U_phase U c = U_phase U' c' := by aesop

lemma phase_comm (c c' : phase) :
  c * c' = c' * c := by
  apply phase_ext
  rcases c with ⟨a, b⟩
  rcases c' with ⟨a', b'⟩
  simp; ring

-- mutual induction is fun :)
lemma anticommuteₘ_correct {n} (m m' : Fin n -> Pauli) :
  let kron_m := unitary_n_nkron (λ i => (m i).val)
  let kron_m' := unitary_n_nkron (λ i => (m' i).val)
  (anticommuteₘ m m' -> (kron_m * kron_m' = -kron_m' * kron_m)) ∧
  (!(anticommuteₘ m m') -> (kron_m * kron_m' = kron_m' * kron_m)) := by
  simp
  induction n with
  | zero =>
    simp [unitary_n_nkron, anticommuteₘ]
  | succ n₀ IH =>
    have IHL m m' := (IH m m').left
    have IHR m m' := (IH m m').right
    clear IH
    constructor
    all_goals
      intro H
      simp only [unitary_n_nkron_iter]
      simp only [mul_nkrons]
      by_cases head_commute : commute₁ (m 0) (m' 0)
    all_goals
      simp only [mul_Pauli1_correct]
      have Htail := H
      simp [anticommuteₘ, head_commute] at Htail
      have H' (A : Fin (n₀+1) -> Pauli):
        Fin.tail (λ i => (A i).val) = Fin.tail (λ i => A i)
      · apply funext
        intro x
        simp [Fin.tail]
      rw [H' m]
      rw [H' m']
      clear H'
      rw [commute₁_right]
    · have IH := (IHL (Fin.tail m) (Fin.tail m') Htail)
      simp at IH
      rw [IH]
      simp only [neg_is_uphase]
      simp only [uphase_of_kron, uphase_of_kron_right, uphase_of_uphase]
      rw [commute₁_correct_true] <;> try assumption
      apply uphase_ext; try rfl
      apply phase_comm
    · have IH := (IHR (Fin.tail m) (Fin.tail m') Htail)
      simp at IH
      rw [IH]
      rw [commute₁_correct_false]
      swap; simp_all only [Bool.not_eq_true]
      simp only [neg_is_uphase]
      simp only [uphase_of_kron_right, uphase_of_uphase]
      apply uphase_ext; try rfl
      rw [neg_pgphaseE]
      simp [neg_pphase, phase_n1, neg_phaseE, neg_phase]
    · have IH := (IHR (Fin.tail m) (Fin.tail m') Htail)
      simp at IH
      rw [IH]
      rw [commute₁_correct_true]; try assumption
    · have IH := (IHL (Fin.tail m) (Fin.tail m') Htail)
      simp at IH
      rw [IH]
      rw [commute₁_correct_false]
      swap; simp_all only [Bool.not_eq_true]
      simp only [neg_is_uphase]
      simp only [uphase_of_kron, uphase_of_kron_right, uphase_of_uphase]
      apply uphase_ext; try rfl
      simp [phase_n1, neg_pgphaseE, neg_pphase, neg_phaseE, neg_phase]

lemma anticommuteₘ_correct_true {n} (m m' : Fin n -> Pauli)
  (H: anticommuteₘ m m') :
  let kron_m := unitary_n_nkron (λ i => (m i).val)
  let kron_m' := unitary_n_nkron (λ i => (m' i).val)
  (kron_m * kron_m' = -kron_m' * kron_m) := by
  have H' := anticommuteₘ_correct m m'
  simp at H'
  have H'' := (H'.left H)
  simp [H'']

lemma anticommuteₘ_correct_false {n} (m m' : Fin n -> Pauli)
  (H: anticommuteₘ m m' = false) :
  let kron_m := unitary_n_nkron (λ i => (m i).val)
  let kron_m' := unitary_n_nkron (λ i => (m' i).val)
  (kron_m * kron_m' = kron_m' * kron_m) := by
  have H' := anticommuteₘ_correct m m'
  simp at H'
  have H'' := (H'.right H)
  simp [H'']

lemma anticommuteₘ_cat {n₁ n₂}
  (m₁ m₁' : Fin n₁ -> Pauli)
  (m₂ m₂' : Fin n₂ -> Pauli) :
  anticommuteₘ (cast_fin_append m₁ m₂) (cast_fin_append m₁' m₂') =
  (anticommuteₘ m₁ m₁' ^^ anticommuteₘ m₂ m₂') := by
  induction n₁ with
  | zero =>
    simp [anticommuteₘ]
    -- this is terrible
    induction n₂ with
    | zero => simp [anticommuteₘ]
    | succ n₀ IH =>
      simp [anticommuteₘ, cast_fin_append, Fin.append, Fin.addCases]
      simp [cast_fin_append_iter2, IH]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [cast_fin_append_iter1]
    simp [IH]

lemma anticommuteₘ_sym (m₁ m₂ : Fin n -> Pauli) :
  anticommuteₘ m₁ m₂ = anticommuteₘ m₂ m₁ := by
  induction n with
  | zero => simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    rw [IH]
    suffices: commute₁ (m₁ 0) (m₂ 0) = commute₁ (m₂ 0) (m₁ 0)
    · rw [this]
    rw [Bool.eq_iff_iff]
    rw [commute₁_sym]

lemma anticommuteₘ_xx (m : Fin n -> Pauli) :
  anticommuteₘ m m = false := by
  induction n with
  | zero =>
    simp [anticommuteₘ]
  | succ n₀ IH =>
    simp [anticommuteₘ]
    simp [IH]
    rw [commute₁_xx]


def anticommute {n : ℕ} (U₁ U₂ : PauliGroup n) :=
  anticommuteₘ (PauliGroup.map U₁) (PauliGroup.map U₂)

lemma anticommute_kron {n₁ n₂}
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  anticommute (kronOfPauli U₁ U₂) (kronOfPauli U₁' U₂') =
  (anticommute U₁ U₁' ^^ anticommute U₂ U₂') := by
  unfold anticommute
  rw [map_kron_of_Pauli]
  rw [map_kron_of_Pauli]
  rw [anticommuteₘ_cat]
  rw [Bool.xor_comm]

lemma anticommute_sym (U₁ U₂ : PauliGroup n) :
  anticommute U₁ U₂ = anticommute U₂ U₁ := by
  unfold anticommute
  rw [anticommuteₘ_sym]

lemma anticommute_xx (P : PauliGroup n) :
  anticommute P P = false := by
  unfold anticommute
  rw [anticommuteₘ_xx]

lemma uphase_mul_left {n} c (P Q : 𝐔ₙ[n]) :
  U_phase P c * Q = U_phase (P * Q) c := by
  rcases Q with ⟨Q₀, HQ⟩
  simp [U_phase]

lemma anticommute_correct_true {n} (P Q : PauliGroup n)
  (H: anticommute P Q) :
  P.val * Q.val = -Q.val * P.val := by
  let FP := foldPauli.symm P
  let FQ := foldPauli.symm Q
  have PE : P = foldPauli FP := by
    rw [Equiv.apply_symm_apply]
  have QE : Q = foldPauli FQ := by
    rw [Equiv.apply_symm_apply]
  simp [PE, QE]
  clear PE QE
  let cP := FP.1
  let mP := FP.2
  have FPE : FP = (cP, mP) := by rfl
  let cQ := FQ.1
  let mQ := FQ.2
  have FQE : FQ = (cQ, mQ) := by rfl
  simp [FPE, FQE]
  clear FPE FQE
  simp [foldPauli, fold, fold_aux]
  simp only [<- mul_Uphases]
  rw [anticommuteₘ_correct_true]
  swap
  · simp [anticommute] at H
    rw [PauliGroup.map] at H
    aesop
  simp only [neg_is_uphase]
  rw [uphase_mul_left]
  simp only [uphase_of_uphase]
  apply uphase_ext <;> try rfl
  rw [phase_comm]
  suffices: cP.val * cQ.val = cQ.val * cP.val
  · rw [this]
  rw [phase_comm]

lemma anticommute_correct_false {n} (P Q : PauliGroup n)
  (H: anticommute P Q = false) :
  P.val * Q.val = Q.val * P.val := by
  let FP := foldPauli.symm P
  let FQ := foldPauli.symm Q
  have PE : P = foldPauli FP := by
    rw [Equiv.apply_symm_apply]
  have QE : Q = foldPauli FQ := by
    rw [Equiv.apply_symm_apply]
  simp [PE, QE]
  clear PE QE
  let cP := FP.1
  let mP := FP.2
  have FPE : FP = (cP, mP) := by rfl
  let cQ := FQ.1
  let mQ := FQ.2
  have FQE : FQ = (cQ, mQ) := by rfl
  simp [FPE, FQE]
  clear FPE FQE
  simp [foldPauli, fold, fold_aux]
  simp only [<- mul_Uphases]
  rw [anticommuteₘ_correct_false]
  swap
  · simp [anticommute] at H
    rw [PauliGroup.map] at H
    aesop
  apply uphase_ext <;> try rfl
  rw [phase_comm]
