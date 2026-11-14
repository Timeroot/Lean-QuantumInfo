import LeanQEC.Stabilizer.Basic
import LeanQEC.QuantumInfoSkeleton

/-
IMPORTANT: This file is kinda ruined until i refactor to deal
with how i rewrote the stabilizer code definition.
Here be dragons
-/

noncomputable section

def three_qubit_encode:= fun (ψ : PState 1) =>
  (((ψ ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply
    (Cₙ[pX] ⊗ₙ p1)).apply
    (Cₙ[p1 ⊗ₙ pX])


noncomputable section AristotleLemmas

/-
If the control qubit is |0>, the controlled unitary Cₙ[U] acts as the identity.
-/
open Qubit Function Matrix

lemma control_zero_stab {n : ℕ} (U : 𝐔ₙ[n]) (ψ : PState n) :
  (qub_zero ⊗ₚ ψ).apply (Cₙ[U]) = qub_zero ⊗ₚ ψ := by
    unfold PState.apply n_controllize Qubit.controllize PState.kron qub_zero; simp +decide [ Finset.sum_ite ] ;
    ext ; aesop;
    unfold unitary_fin_equiv ket_prod; simp +decide [ Matrix.mulVec, dotProduct ] ;
    rw [ Finset.sum_eq_single x ] <;> aesop;
    · unfold normalized_kron; aesop;
      simp_all +decide [ toMat, Matrix.submatrix ];
      unfold fin2prodbitvec_equiv at h; aesop;
    · cases Fin.exists_fin_two.mp ⟨ ( fin2prodbitvec_equiv.symm x ).1, rfl ⟩ <;> tauto;
    · cases a_1 ( fin2prodbitvec_equiv.symm.injective <| Prod.ext ( by aesop ) a.symm );
    · simp_all +decide [ toMat, normalized_kron ];
      unfold fin2prodbitvec_equiv at * ; aesop

/-
If the control qubit is |1>, the controlled unitary Cₙ[U] applies U to the target.
-/
open Qubit Function Matrix

lemma control_one_apply {n : ℕ} (U : 𝐔ₙ[n]) (ψ : PState n) :
  (qub_one ⊗ₚ ψ).apply (Cₙ[U]) = qub_one ⊗ₚ (ψ.apply U) := by
    -- Unfold `PState.apply`, `n_controllize`, and `Qubit.controllize`.
    unfold PState.apply
    unfold n_controllize
    unfold Qubit.controllize;
    unfold qub_one PState.kron; aesop;
    ext x;
    unfold unitary_fin_equiv ket_prod; aesop;
    unfold normalized_kron; aesop;
    simp +decide [ Matrix.mulVec, dotProduct, Finset.sum_ite ];
    simp +decide [ Finset.filter_and ];
    split_ifs <;> simp +decide [ * ];
    · aesop;
    · rw [ Finset.sum_eq_single x ] <;> aesop;
      · simp_all +decide [ Matrix.submatrix, Matrix.kroneckerMap ];
        simp +decide [ toMat, Matrix.of_apply ];
        simp_all +decide [ fin2prodbitvec_equiv, bits_cat ];
      · cases a_1 ( fin2prodbitvec_equiv.symm.injective <| Prod.ext ( by aesop ) ( by aesop ) );
    · simp_all +decide [ Matrix.submatrix ];
      simp_all +decide [ toMat, Matrix.mulVec, dotProduct, Finset.sum_ite ];
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_bij ( fun y hy => ( fin2prodbitvec_equiv.symm y ).2 ) _ _ _ _ <;> simp_all +decide;
      · aesop;
        exact fin2prodbitvec_equiv.symm.injective ( Prod.ext ( by aesop ) ( by aesop ) );
      · intro b; use fin2prodbitvec_equiv ( 1, b ) ; aesop;
      · aesop;
        simp_all +decide [ fin2prodbitvec_equiv ];
    · cases Fin.exists_fin_two.mp ⟨ ( fin2prodbitvec_equiv.symm x ).1, rfl ⟩ <;> contradiction

/-
Encoding |0> yields |000>.
-/
open Qubit Function Matrix

lemma three_qubit_encode_zero : three_qubit_encode qub_zero = (qub_zero ⊗ₚ qub_zero) ⊗ₚ qub_zero := by
  -- Apply the first controlled-X operation to the first two qubits.
  have h1 : ((qub_zero ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply (Cₙ[pX] ⊗ₙ 1) = qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero := by
    have h1 : ((qub_zero ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply (Cₙ[pX] ⊗ₙ 1) = ((qub_zero ⊗ₚ qub_zero).apply (Cₙ[pX])) ⊗ₚ (qub_zero.apply 1) := by
      exact kron_mul_kron (qub_zero ⊗ₚ qub_zero) qub_zero Cₙ[pX] 1;
    rw [ h1, control_zero_stab ];
    -- The identity operator acts as the identity on the ket, so applying it to qub_zero should just give qub_zero back.
    rw [PState.apply_id, PState.kron_assoc]
  convert control_zero_stab ( p1 ⊗ₙ pX ) ( qub_zero ⊗ₚ qub_zero ) using 1;
  · unfold three_qubit_encode
    congr
  · rw [PState.kron_assoc]

/-
Applying Pauli X to |0> yields |1>.
-/
open Qubit Function Matrix

@[simp]
lemma qub_zero_apply_X : qub_zero.apply pX = qub_one := by
  ext i; fin_cases i ; simp +decide [ qub_zero, qub_one, pX ] ;
  · unfold unitary_fin_equiv; aesop;
    convert rfl;
    ext i ; fin_cases i <;> norm_num [ Matrix.mulVec, dotProduct ];
    · simp ( config := { decide := Bool.true } ) [ Qubit.X ];
      simp ( config := { decide := Bool.true } ) [ beq ];
      simp ( config := { decide := Bool.true } ) [ BitVec.equivFin ];
      exact Or.inl rfl;
    · simp ( config := { decide := Bool.true } ) [ Qubit.X ];
      simp ( config := { decide := Bool.true } ) [ beq ];
      field_simp;
      erw [ Matrix.cons_val_zero, Matrix.cons_val_one ] ; norm_num;
  · unfold qub_zero qub_one PState.apply; norm_num [ Matrix.mulVec ] ;
    unfold pX;
    unfold Qubit.X;
    simp ( config := { decide := true } );
    exact show ( Matrix.mulVec ( Matrix.of ![![0, 1], ![1, 0]] ) ![1, 0] ) 1 = 1 by simp ( config := { decide := Bool.true } ) [ Matrix.mulVec ] ;

/-
Helper lemma: applying I ⊗ X to |10> yields |11>.
-/
open Qubit Function Matrix

lemma helper_step_encode_one : (qub_one ⊗ₚ qub_zero).apply (p1 ⊗ₙ pX) = qub_one ⊗ₚ qub_one := by
  have h_step : (qub_one ⊗ₚ qub_zero).apply (p1 ⊗ₙ pX) = (qub_one.apply p1) ⊗ₚ (qub_zero.apply pX) := by
    exact kron_mul_kron qub_one qub_zero p1 pX;
  have h_p1 : qub_one.apply p1 = qub_one := by
    exact one_stab_all _
  have h_pX : qub_zero.apply pX = qub_one := by
    exact qub_zero_apply_X
  rw [h_step, h_p1, h_pX]

/-
Encoding |1> yields |111>.
-/
open Qubit Function Matrix

lemma three_qubit_encode_one : three_qubit_encode qub_one = (qub_one ⊗ₚ qub_one) ⊗ₚ qub_one := by
  -- The state after applying the first operation is `(qub_one ⊗ₚ qub_one) ⊗ₚ qub_zero`.
  have h_first_op : ((qub_one ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply ((Cₙ[pX]) ⊗ₙ p1) = (qub_one ⊗ₚ qub_one) ⊗ₚ qub_zero := by
    -- Apply the controlled X gate to the first and second qubits.
    have h1 : (qub_one ⊗ₚ qub_zero).apply (Cₙ[pX]) = qub_one ⊗ₚ qub_one := by
      exact control_one_apply pX qub_zero ▸ qub_zero_apply_X ▸ rfl;
    -- Apply the identity matrix to the third qubit.
    have h2 : qub_zero.apply p1 = qub_zero := by
      simp +decide [ PState.apply ];
      ext ; norm_num [ p1 ];
    -- Apply the definition of `apply` to split the operation.
    have h_split : ((qub_one ⊗ₚ qub_zero) ⊗ₚ qub_zero).apply ((Cₙ[pX]) ⊗ₙ p1) = ((qub_one ⊗ₚ qub_zero).apply (Cₙ[pX])) ⊗ₚ (qub_zero.apply p1) := by
      exact kron_mul_kron (qub_one ⊗ₚ qub_zero) qub_zero Cₙ[pX] p1;
    rw [ h_split, h1, h2 ];
  -- The state after applying the second operation is `(qub_one ⊗ₚ qub_one) ⊗ₚ qub_one`.
  have h_second_op : ((qub_one ⊗ₚ qub_one) ⊗ₚ qub_zero).apply (Cₙ[p1 ⊗ₙ pX]) = (qub_one ⊗ₚ (qub_one ⊗ₚ qub_one)) := by
    rw [ PState.kron_assoc ];
    rw [ control_one_apply ];
    exact congr_arg _ ( helper_step_encode_one );
  -- By the associativity of the tensor product, we can rewrite the right-hand side to match the left-hand side.
  have h_assoc : (qub_one ⊗ₚ qub_one) ⊗ₚ qub_one = qub_one ⊗ₚ (qub_one ⊗ₚ qub_one) := by
    exact PState.kron_assoc;
  exact h_assoc ▸ h_second_op ▸ h_first_op ▸ rfl

/-
The tensor product of state vectors is linear in the first argument.
-/
open Qubit Function Matrix

/-
Any 1-qubit state vector can be written as a linear combination of |0> and |1>.
-/
open Qubit Function Matrix

lemma vec_eq_linear_combo (ψ : PState 1) : ψ.vec = ψ 0 • qub_zero.vec + ψ 1 • qub_one.vec := by
  ext x; fin_cases x <;> norm_num [ qub_zero, qub_one ] ;
  · exact show ψ.vec 0 = ψ.vec 0 * 1 + ψ.vec 1 * 0 by ring;
  · exact show ψ.vec 1 = ψ.vec 0 * 0 + ψ.vec 1 * 1 by ring;

/-
Define a vector-only version of the encoding map and prove it matches the PState version.
-/
open Qubit Function Matrix

noncomputable def encode_vec (v : BitVec 1 → ℂ) : BitVec 3 → ℂ :=
  let v0 := ket_prod (ket_prod v qub_zero.vec) qub_zero.vec
  let v1 := (Cₙ[pX] ⊗ₙ p1).1.mulVec v0
  (Cₙ[p1 ⊗ₙ pX]).1.mulVec v1

lemma three_qubit_encode_eq_encode_vec (ψ : PState 1) :
  (three_qubit_encode ψ).vec = encode_vec ψ.vec := by
    unfold three_qubit_encode;
    unfold encode_vec; aesop;

/-
The vector encoding function is linear.
-/
open Qubit Function Matrix

lemma encode_vec_linear (v w : BitVec 1 → ℂ) (a b : ℂ) :
  encode_vec (a • v + b • w) = a • encode_vec v + b • encode_vec w := by
    unfold encode_vec;
    simp +decide [ ket_prod_linear_left ];
    rw [ Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul ]

end AristotleLemmas

lemma three_qubit_encode_correct (ψ : PState 1) : three_qubit_encode ψ =
  PState.sum (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  (qub_one ⊗ₚ qub_one ⊗ₚ qub_one) (ψ 0) (ψ 1) (single_qub_normalized _)
  (prod_orth_left zero_one_orth) := by
  -- Apply the linearity of the encoding function to split the sum into the sum of the encoded vectors.
  have h_split : encode_vec ψ.vec = ψ 0 • encode_vec qub_zero.vec + ψ 1 • encode_vec qub_one.vec := by
    rw [ vec_eq_linear_combo, encode_vec_linear ];
  apply Ket.ext;
  -- Apply the equality of vectors from `h_split` to conclude the proof.
  have h_eq : (three_qubit_encode ψ).vec = (ψ 0 • (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).vec + ψ 1 • (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).vec) := by
    convert h_split using 2;
    · congr! 1;
      convert three_qubit_encode_eq_encode_vec qub_zero |> Eq.symm;
      simp +zetaDelta at *;
      convert three_qubit_encode_eq_encode_vec qub_zero using 1;
      rw [ three_qubit_encode_zero ];
      congr! 1;
      exact Eq.symm PState.kron_assoc;
    · rw [ ← three_qubit_encode_eq_encode_vec ];
      rw [ three_qubit_encode_one ];
      congr! 2;
      exact Eq.symm PState.kron_assoc;
  intro x
  exact congrFun h_eq x


lemma beq_eq : (beq.symm 0#1) = 0 := by
  unfold beq
  show (BitVec.equivFin 0#1 = 0)
  simp



@[simp]
lemma qub_zero_Z : qub_zero.apply pZ = qub_zero := by
  simp [PState.apply]
  simp only [qub_zero]
  rw [Ket.mk.injEq]
  unfold Equiv.arrowCongr
  unfold pZ
  simp only [unitary_fin_equiv]
  simp [Qubit.Z]
  simp [Matrix.submatrix_mulVec_equiv]
  congr
  simp [Matrix.vecHead, Matrix.vecTail]

@[simp]
lemma qub_one_Z : qub_one.apply pZ = Ket.phase_mul qub_one ⟨-1, by simp⟩ := by
  simp [PState.apply]
  simp only [qub_one]
  rw [Ket.mk.injEq]
  unfold Equiv.arrowCongr
  unfold pZ
  simp only [unitary_fin_equiv]
  simp [Qubit.Z]
  simp [Matrix.submatrix_mulVec_equiv]
  simp [Matrix.vecHead, Matrix.vecTail]
  simp [Ket.phase_mul]
  rw [<- Pi.neg_comp]
  congr
  aesop

abbrev fold1 {n} (t : Fin n → Pauli) := foldPauli (1, t)

abbrev IXI_pg := fold1 ![Pauli_I, Pauli_X, Pauli_I]
abbrev XII_pg := fold1 ![Pauli_X, Pauli_I, Pauli_I]
abbrev IIX_pg := fold1 ![Pauli_I, Pauli_I, Pauli_X]
abbrev IZZ_pg := fold1 ![Pauli_I, Pauli_Z, Pauli_Z]
abbrev ZZI_pg := fold1 ![Pauli_Z, Pauli_Z, Pauli_I]
--abbrev stab := QCode.stabilizers three_qubit_encode

/-
lemma IZZ_in_stab :
  (fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) ∈
  QCode.stabilizers three_qubit_encode := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    rw [PState.apply_id]
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_I, Pauli_Z, Pauli_Z]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [←PState.kron_assoc, PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]

lemma ZIZ_in_stab : (fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) ∈ stab := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    simp
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_Z, Pauli_I, Pauli_Z]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [←PState.kron_assoc, PState.apply_id]
    nth_rewrite 2 [←@Ket.mul_phase_id _ _ qub_one]
    simp_rw [PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]

lemma ZZI_in_stab : (fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) ∈ stab := by
  intro ψ
  rw [three_qubit_encode_correct]
  unfold stabilizes
  rw [PState.sum_apply]
  have hz : (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero).apply ↑(fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) = (qub_zero ⊗ₚ qub_zero ⊗ₚ qub_zero)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_zero_Z]
    simp
  have ho : (qub_one ⊗ₚ qub_one ⊗ₚ qub_one).apply ↑(fold1 ![Pauli_Z, Pauli_Z, Pauli_I]) = (qub_one ⊗ₚ qub_one ⊗ₚ qub_one)
  · unfold fold1 foldPauli
    simp [-PState.apply]
    unfold fold fold_aux
    simp [-PState.apply, U_phase, phase_id_coe, unitary_n_nkron]
    rw [unitary1_kron_assoc, kron_mul_kron, kron_mul_kron]
    simp_rw [Pauli_Z, Pauli_I, qub_one_Z]
    simp_rw [PState.phase_prod_phase]
    simp [Ket.phase_mul]
  simp_rw [hz, ho]
-/

lemma commute₁_XZ : commute₁ Pauli_X Pauli_Z = false := by simp [commute₁]

lemma pphase_IXI_IZZ : pauli_pauli_phase IXI_pg IZZ_pg = pgphase_n1 := by
   simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_XII_IZZ : pauli_pauli_phase XII_pg IZZ_pg = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_XII_ZZI : pauli_pauli_phase XII_pg ZZI_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IIX_IZZ : pauli_pauli_phase IIX_pg IZZ_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IIX_ZZI : pauli_pauli_phase IIX_pg ZZI_pg = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_IXI_ZZI : pauli_pauli_phase IXI_pg ZZI_pg = pgphase_n1 := by
  simp [pauli_pauli_phase, anticommute, PauliGroup.map,
   anticommuteₘ, Fin.tail, commute₁]

lemma pphase_pauli1 {n : ℕ} {p : PauliGroup n} :
  pauli_pauli_phase Pauli1 p = pgphase_1 := by
  unfold pauli_pauli_phase anticommute
  -- Since the first element is Pauli_I, which commutes with any Pauli matrix, the condition is false. Therefore, the else part is executed, which is pgphase_1.
  simp [PauliGroup.map];
  -- Since the first element is Pauli_I, which commutes with any Pauli matrix, the condition is false. Therefore, the else part is executed, which is pgphase_1. Hence, the implication holds trivially.
  simp [Pauli1_unfold];
  -- Since Pauli_I is the identity matrix, it commutes with any other matrix, including itself. Therefore, anticommuteₘ should be false.
  have h_comm : ∀ (m : Fin n → Pauli), anticommuteₘ (fun _ => Pauli_I) m = false := by
    induction' n with n ih <;> simp +decide [ *, anticommuteₘ ];
    -- Since the tail of the sequence is all identities, the anticommuteₘ of the tail with any m is false.
    intros m
    simp [commute₁];
    convert ih ( Fin.tail m ) using 1;
    exact ⟨ 1, mem_PauliGroup_id ⟩;
  aesop


lemma pauli_weight_one_contra {n : ℕ} {E : PauliGroup n}
(hpw : pauli_weight E ≤ 1)
 (i₁ i₂ : Fin n) (hne : i₁ ≠ i₂): ((PauliGroup.map E) i₁ = Pauli_I) ∨ ((PauliGroup.map E) i₂ = Pauli_I) := by
  by_cases heq₁: ((PauliGroup.map E) i₁ = Pauli_I)
  · exact Or.inl heq₁
  by_cases heq₂ : ((PauliGroup.map E) i₂ = Pauli_I)
  · exact Or.inr heq₂
  unfold pauli_weight PauliGroup.map at hpw
  have hsub: {i₁, i₂} ⊆ ({i | (PauliGroup.map E) i ≠ Pauli_I} : Finset (Fin n))
  · rintro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl <;> assumption
  apply absurd hpw (not_le_of_gt (lt_of_lt_of_le one_lt_two _))
  convert (Finset.card_le_card hsub)
  symm
  rw [Finset.card_eq_two]
  refine ⟨i₁, i₂, hne, rfl⟩

lemma pauli_only_X_contra_Y {n : ℕ} {E : PauliGroup n}
(hpo : pauli_only E Pauli_X) {i : Fin n} :
  (PauliGroup.map E) i ≠ Pauli_Y := by
  unfold pauli_only at hpo
  have hpoi:= hpo i
  unfold PauliGroup.map at hpoi
  rcases hpoi with hi | hx
  · exact fun hf => pgYnepgI (hf.symm.trans hi)
  exact fun hf => pgXnepgY (hx.symm.trans hf)

lemma pauli_only_X_contra_Z {n : ℕ} {E : PauliGroup n}
(hpo : pauli_only E Pauli_X) {i : Fin n} :
  (PauliGroup.map E) i ≠ Pauli_Z := by
  unfold pauli_only at hpo
  have hpoi:= hpo i
  unfold PauliGroup.map at hpoi
  rcases hpoi with hi | hx
  · exact fun hf => pgZnepgI (hf.symm.trans hi)
  exact fun hf => pgXnepgZ (hx.symm.trans hf)

/-
theorem three_qub_corrects_one_x : QCode.unique_corrects_P_error_of_weight three_qubit_encode 1
 ⟨pX, by simp[Pauli]⟩ := by
  intros E₁ E₂ only_E₁ only_E₂ p1_E₁ p1_E₂ hW₁ hW₂ hne
  have h_or :
    ∀ E,
    pauli_only E Pauli_X →
    PauliGroup.phase E = pgphase_1 →
    pauli_weight E ≤ 1 →
    E = fold1 ![Pauli_X, Pauli_I, Pauli_I] ∨
    E = fold1 ![Pauli_I, Pauli_X, Pauli_I] ∨
    E = fold1 ![Pauli_I, Pauli_I, Pauli_X] ∨
    E = Pauli1 := by
      intro E
      let pm := PauliGroup.map E
      let pp := PauliGroup.phase E
      intro hpo hpp hpw
      rcases (Pauli_cases (pm 0)) with h0x | hf | hf | h0i <;>
      rcases (Pauli_cases (pm 1)) with h1x | hf | hf | h1i
      · rcases (pauli_weight_one_contra hpw 0 1 (by norm_num)) with h0I | h1I
        · apply absurd (h0x.symm.trans h0I) pgXnepgI
        apply absurd (h1x.symm.trans h1I) pgXnepgI
      all_goals rcases (Pauli_cases (pm 2)) with h2x | hf | hf | h2i
      all_goals try apply absurd hf (pauli_only_X_contra_Y hpo)
      all_goals try apply absurd hf (pauli_only_X_contra_Z hpo)
      · rcases (pauli_weight_one_contra hpw 0 2 (by simp)) with h0I | h1I
        · apply absurd (h0x.symm.trans h0I) pgXnepgI
        apply absurd (h2x.symm.trans h1I) pgXnepgI
      · left
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · rcases (pauli_weight_one_contra hpw 1 2 (by simp)) with h1I | h2I
        · apply absurd (h1x.symm.trans h1I) pgXnepgI
        apply absurd (h2x.symm.trans h2I) pgXnepgI
      · apply Or.inr (Or.inl _)
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · apply (Or.inr (Or.inr (Or.inl _)))
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
      · apply (Or.inr (Or.inr (Or.inr _))) --wait, not actually sure how to do this
        rw [Pauli1_unfold]
        apply Equiv.injective foldPauli.symm
        ext1
        · simp only [Equiv.symm_apply_apply]
          congr
        simp only [Equiv.symm_apply_apply]
        ext1 x
        fin_cases x <;> assumption
  rcases h_or E₁ only_E₁ p1_E₁ hW₁ with rfl | rfl | rfl | rfl
  all_goals rcases h_or E₂ only_E₂ p1_E₂ hW₂ with rfl | rfl | rfl | rfl
  all_goals rw [QCode.distinguishes_of_exists_dist_stab]
  · contradiction --case where errors are identical
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --XII, IXI
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --XII, IIX
    simp [pphase_XII_IZZ, pphase_IIX_IZZ]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --XII, III
    simp [pphase_XII_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IXI, XII
    simp [pphase_XII_IZZ, pphase_IXI_IZZ]
    norm_num
  · contradiction
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, IIX
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, III
    simp [pphase_IXI_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --XII, IIX
    simp [pphase_XII_ZZI, pphase_IIX_ZZI]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IIX, IXI
    simp [pphase_IXI_ZZI, pphase_IIX_ZZI]
    norm_num
  · contradiction
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IIX, III
    simp [pphase_IIX_IZZ, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IIX, III
    simp [pphase_XII_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_Z, Pauli_Z, Pauli_I], ZZI_in_stab⟩ --IXI, III
    simp [pphase_IXI_ZZI, pphase_pauli1]
    norm_num
  · exists ⟨fold1 ![Pauli_I, Pauli_Z, Pauli_Z], IZZ_in_stab⟩ --IIX, III
    simp [pphase_IIX_IZZ, pphase_pauli1]
    norm_num
  contradiction
-/
