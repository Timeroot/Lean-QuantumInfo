import LeanQEC.AI_Generated.Pauli1Mul

noncomputable section

def pointwise_mul_Paulis {n} (P Q : Fin n -> Pauli) (i : Fin n) :=
  mul_Pauli1 (P i) (Q i)

def fold_Paulis_with_phases {n} (P : Fin n -> (pgroup_phases × Pauli)) :=
  unitary_n_nkron (λ i => U_phase (P i).2 (P i).1)

lemma pointwise_mul_Paulis_correct {n} (P Q : Fin n -> Pauli) :
  fold_Paulis_with_phases (pointwise_mul_Paulis P Q) =
  unitary_n_nkron P * unitary_n_nkron Q := by
  rw [<- mul_unitary_n_nkrons]
  rw [fold_Paulis_with_phases]
  simp [pointwise_mul_Paulis, mul_Pauli1_correct]

def fold_pgroup_phases {n} (lst : Fin n -> pgroup_phases) :=
  match n with
  | 0 => 1
  | _ + 1 => lst 0 * fold_pgroup_phases (Fin.tail lst)

lemma fold_pgroup_phases_empty (lst : Fin 0 -> pgroup_phases) :
  fold_pgroup_phases lst = 1 := by rfl

def collect_phases {n} (P : Fin n -> (pgroup_phases × Pauli)) : factored_Pauli n :=
  (fold_pgroup_phases (λ i => (P i).1), (λ i => (P i).2))

def zip {n t u} (x : Fin n -> t) (y : Fin n -> u) (i : Fin n) : t × u :=
  (x i, y i)

def unzipL {n t u} (xy : Fin n -> (t × u)) (i : Fin n) : t := (xy i).1

def unzipR {n t u} (xy : Fin n -> (t × u)) (i : Fin n) : u := (xy i).2

lemma unzipL_zip {n t u} (x : Fin n -> t) (y : Fin n -> u) i :
  (zip x y i).1 = x i := by rfl

lemma fold_collect_iter {n} (c : Fin (n + 1) -> pgroup_phases) (m : Fin (n + 1) -> Pauli) :
  (foldPauli (collect_phases (zip c m))).val =
  unitary_nkron
    (foldPauli (collect_phases (zip (Fin.tail c) (Fin.tail m))))
    (U_phase (m 0).val (c 0)) := by
    simp [foldPauli, fold, fold_aux, collect_phases]
    simp [unitary_n_nkron]
    rw [U_phase_tensor]
    congr
    simp [unzipL_zip, fold_pgroup_phases]
    group

lemma fold_Paulis_with_phases_iter {n} (P : Fin (n + 1) -> pgroup_phases × Pauli) :
  fold_Paulis_with_phases P =
  unitary_nkron (fold_Paulis_with_phases (Fin.tail P)) (U_phase (P 0).2 (P 0).1) := by
  simp [fold_Paulis_with_phases, unitary_n_nkron]
  rfl

lemma unitary_n_nkron_empty (P : Fin 0 -> 𝐔ₙ[1]) :
  unitary_n_nkron P = 1 := by rw [unitary_n_nkron]

lemma collect_phases_correct_aux {n}
  (c : Fin n -> pgroup_phases) (m : Fin n -> Pauli) :
  (foldPauli (collect_phases (zip c m))) = fold_Paulis_with_phases (zip c m) := by
  induction n with
  | zero =>
    simp [foldPauli, fold, fold_Paulis_with_phases, fold_aux]
    simp [collect_phases, fold_pgroup_phases]
    simp [unitary_n_nkron_empty]
    have: (1 : pgroup_phases) = phase_id := by
      simp [OfNat.ofNat, One.one]
    rw [this]
    rw [U_phase_id]
  | succ n₀ IH =>
    rw [fold_collect_iter]
    rw [fold_Paulis_with_phases_iter]
    rw [IH]
    congr

lemma collect_phases_correct {n} (P : Fin n -> (pgroup_phases × Pauli)) :
  (foldPauli (collect_phases P)) = fold_Paulis_with_phases P := by
  let c := unzipL P
  let m := unzipR P
  have H: P = zip c m := by
    simp only [c, m]
    rfl
  simp [H]
  apply collect_phases_correct_aux

def mul_Pauli1_tuples {n} (P Q : Fin n -> Pauli) : factored_Pauli n :=
  collect_phases (pointwise_mul_Paulis P Q)

lemma mul_Pauli1_tuples_correct {n} (P Q : Fin n -> Pauli) :
  (foldPauli (mul_Pauli1_tuples P Q)).val =
  unitary_n_nkron P * unitary_n_nkron Q := by
  rw [mul_Pauli1_tuples]
  rw [collect_phases_correct]
  rw [pointwise_mul_Paulis_correct]

def scale_factored_Pauli {n} (c : pgroup_phases) (P : factored_Pauli n) :=
  (c * P.1, P.2)

def mul_factored_Paulis {n} (P Q : factored_Pauli n) :=
  scale_factored_Pauli (P.1 * Q.1) (mul_Pauli1_tuples P.2 Q.2)

lemma mul_factored_Paulis_correct {n} (P Q : factored_Pauli n) :
  foldPauli (mul_factored_Paulis P Q) =
  (foldPauli P).val * (foldPauli Q).val := by
  rw [mul_factored_Paulis]
  rw [scale_factored_Pauli]
  rw [mul_comm_pgroup_phases]
  rw [fold_pauli_mul]
  rw [mul_Pauli1_tuples_correct]
  simp [foldPauli, fold, fold_aux]
  rw [<- mul_Uphases]
  congr

def mul_Paulis {n} (P Q : PauliGroup n) :=
  foldPauli (mul_factored_Paulis (foldPauli.symm P) (foldPauli.symm Q))

lemma mul_Paulis_correct {n} (P Q : PauliGroup n) :
  mul_Paulis P Q = P.val * Q.val := by
  let PF := foldPauli.symm P
  let QF := foldPauli.symm Q
  have PE : P = foldPauli PF := by aesop
  have QE : Q = foldPauli QF := by aesop
  simp [PE, QE]
  simp [mul_Paulis]
  apply mul_factored_Paulis_correct

lemma mul_Pauli1_xx (P : Pauli) :
  mul_Pauli1 P P = (1, Pauli_I) := by
  rw [mul_Pauli1]
  rcases (Pauli_cases P) with rfl | rfl | rfl | rfl
  all_goals aesop

lemma pointwise_mul_Paulis_xx {n} (P : Fin n -> Pauli) :
  pointwise_mul_Paulis P P = (λ _ => (1, Pauli_I)) := by
  unfold pointwise_mul_Paulis
  apply funext
  intro x
  apply mul_Pauli1_xx

lemma collect_phases_iter {n} (P : Fin (n + 1) -> (pgroup_phases × Pauli)) :
  collect_phases P =
  ((P 0).1 * (collect_phases (Fin.tail P)).1, λ i => (P i).2) := by
  rw [collect_phases, collect_phases]
  rfl

lemma mul_Pauli1_tuples_xx {n} (P : Fin n -> Pauli) :
  mul_Pauli1_tuples P P = unfolded1 := by
  rw [mul_Pauli1_tuples]
  rw [pointwise_mul_Paulis_xx]
  clear P
  induction n with
  | zero =>
    simp [collect_phases, fold_pgroup_phases]
    rfl
  | succ n₀ IH =>
    simp [collect_phases_iter]
    conv =>
      enter[1]
      enter[1]
      enter[1]
      enter[1]
      change (λ _ => (1, Pauli_I))
    rw [IH]
    rfl
