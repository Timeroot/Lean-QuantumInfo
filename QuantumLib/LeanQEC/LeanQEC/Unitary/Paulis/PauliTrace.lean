import LeanQEC.Unitary.Paulis.PauliFolding

open Matrix

noncomputable section

variable {n : ℕ}

lemma trace_pauli_single (p : Pauli) :
    Matrix.trace ((p : 𝐔ₙ[1]).val) = if p = Pauli_I then (2 : ℂ) else 0 := by
  rcases Pauli_cases p with ( rfl | rfl | rfl | rfl ) <;> simp +decide [ * ];
  · unfold Pauli_X; norm_num [ Matrix.trace, Matrix.mul_apply ] ;
    unfold pX;
    unfold unitary_fin_equiv; norm_num [ Qubit.X ] ;
    simp +decide [ beq ];
    simp +decide [ BitVec.equivFin ];
  · unfold Pauli_Y;
    unfold pY;
    unfold Qubit.Y; norm_num [ Matrix.trace ] ;
    unfold unitary_fin_equiv; norm_num [ beq ] ;
  · unfold Pauli_Z; norm_num [ Matrix.trace ] ;
    unfold pZ ;
    unfold Qubit.Z; norm_num [ rawZ, unitary_fin_equiv ] ;
    norm_num [ beq ];
  · convert Matrix.trace_one ( n := BitVec 1 )

lemma trace_unitary_nkron {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) :
    Matrix.trace (a ⊗ₙ b).val = Matrix.trace a.val * Matrix.trace b.val := by
  -- The trace is invariant under reindexing. Use `Matrix.trace_reindex` (or `trace_submatrix` with `Equiv.reindexRefl` / symmetry) to show `trace (normalize_mat M) = trace M`.
  have eq_tr : Matrix.trace (a ⊗ₙ b).1 = Matrix.trace (Matrix.kronecker a.val b.val) := by
    rw [unitary_nkron_valE];
    unfold normalize_mat; simp +decide [ Matrix.trace ] ;
    conv_rhs => rw [ ← Equiv.sum_comp bits_cat.symm ] ;
  convert Matrix.trace_kronecker ( a.val ) ( b.val ) using 1

lemma trace_unitary_n_nkron (m : Fin n → 𝐔ₙ[1]) :
    Matrix.trace (unitary_n_nkron m).val = ∏ i, Matrix.trace (m i).val := by
  induction' n with n ih;
  · erw [ Matrix.trace_one ] ; norm_num;
    decide +revert;
  · rw [ Fin.prod_univ_succ, ← ih ];
    convert trace_unitary_nkron _ _ |> Eq.trans <| mul_comm _ _ using 1

lemma prod_if_pauli_I (m : Fin n → Pauli) :
    (∏ i, (if m i = Pauli_I then (2 : ℂ) else 0))
      = if (∀ i, m i = Pauli_I) then (2 : ℂ) ^ n else 0 := by
  split_ifs <;> simp_all +decide [ Finset.prod_ite ]

lemma trace_fold_prod (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = z.1.z * ∏ i, (if m i = Pauli_I then (2 : ℂ) else 0) := by
  convert Matrix.trace_smul ( z.1.z : ℂ ) ( unitary_n_nkron ( fun i => ( m i ).val ) |> Subtype.val ) using 1;
  rw [ trace_unitary_n_nkron ];
  congr! 2;
  convert ( trace_pauli_single ( m ‹_› ) |> Eq.symm ) using 1

lemma trace_fold_eq (z : pgroup_phases) (m : Fin n → Pauli) :
    Matrix.trace (fold (z, m)).val
      = if (∀ i, m i = Pauli_I) then z.1.z * (2 : ℂ) ^ n else 0 := by
  rw [trace_fold_prod, prod_if_pauli_I]
  split <;> simp

end
