import LeanQEC.Unitary.Basic
import LeanQEC.States.Phase
import LeanQEC.AI_Generated.ne0_unitary
import LeanQEC.AI_Generated.scalar_mat_is_one
import LeanQEC.AI_Generated.KronNonsense
import LeanQEC.AI_Generated.PauliBruteForce
import LeanQEC.Unitary.Paulis.Pauli1
import Batteries.Logic
import LeanQEC.Unitary.KronAssoc

open Qubit
open Function

noncomputable section

variable {n : ℕ} (m : Fin n → Pauli)

instance {n : ℕ} : Coe (Fin n → Pauli) (Fin n → ↥𝐔ₙ[1]) where
  coe m := fun i => (m i).val

--i think this doesn't need the injectivity... S.map below can just be changed to S.image
def pauli_embedding {n : ℕ} : (Fin n → Pauli) ↪ (Fin n → ↥𝐔ₙ[1]) where
  toFun := fun m => m
  inj' := by
    intros m₁ m₂ hm
    funext k
    rw [funext_iff] at hm
    have:= hm k
    simp at this
    assumption

instance {n : ℕ} : Coe (Finset (Fin n → Pauli)) (Finset (Fin n → ↥𝐔ₙ[1])) where
  coe S := S.map pauli_embedding

variable {n : ℕ} (m : Fin n → Pauli)

lemma pauli_tensor_hermitian :
  Matrix.IsHermitian (unitary_n_nkron (m : Fin n → 𝐔ₙ[1])).1 := by
  apply herm_of_qubit_tensor_herm
  intro x
  simp [pauli_herm]

--Depend on LeanQuantumInfo i m p o r t s, shelved for the moment
/-
def pauli_tensor_herm : HermitianMat (BitVec n) ℂ :=
  ⟨_, pauli_tensor_hermitian m⟩


def has_pauli_eigenvalues {a : Type*} [Fintype a] [DecidableEq a] {A : Matrix a a ℂ} :=
  ∀ μ, Module.End.HasEigenvalue A.toEuclideanLin μ → (μ = -1 ∨ μ = -1)
-/

--unused, remove?
def is_pauli_product (U : 𝐔ₙ[n]) := ∃ (m : Fin n → Pauli), unitary_n_nkron m = U

--unused, remove?
noncomputable def pauli_n_univ : Finset (Fin n → Pauli) := Finset.univ

--also unused?
noncomputable def pauli_products_n : Finset (𝐔ₙ[n]) := Finset.image (λ m => unitary_n_nkron m) (Finset.univ : Finset (Fin n → Pauli))

def fold_aux (z : pgroup_phases) (m : Fin n → Pauli) :=
  U_phase (unitary_n_nkron (m : Fin n → 𝐔ₙ[1])) z

lemma fold_aux_iter (z : pgroup_phases) (m : Fin (n + 1) → Pauli) :
  fold_aux z m = unitary_nkron (fold_aux z (Fin.tail m)) (m 0) := by
  rw [fold_aux, unitary_n_nkron.eq_def, fold_aux, uphase_of_kron]
  rfl

lemma tuple_eqE_by_cons {n} {u : Type}
  (t t' : Fin (n + 1) → u)
  (eq_head : t 0 = t' 0)
  (eq_tail : Fin.tail t = Fin.tail t') :
  t = t' := by
  apply (Fin.consEquiv (fun _ => u)).symm.injective
  simp; constructor <;> assumption

lemma injective_fold_aux {z z' : pgroup_phases} {m m' : Fin n → Pauli} :
  fold_aux z m = fold_aux z' m' →
  z = z' ∧ m = m' := by
  intro H
  induction n with
  | zero =>
    constructor
    · simp [fold_aux, unitary_n_nkron, U_phase] at H
      rw [Subtype.mk.injEq, phase.mk.injEq]
      convert H
    funext x ; apply finZeroElim x
  | succ n ih =>
  replace H := by simpa [fold_aux_iter] using H
  apply (congrArg (fun a => a.1)) at H
  rename_i H'; clear H'
  simp_rw [unitary_nkron_valE] at H
  apply normalize_mat_ext at H
  have ⟨w, HTails, HHeads⟩ :=
    kron_injective_up_to_scalar H ?_ ?_
  rotate_left
  · apply ne0_unitary; simp
  · apply ne0_unitary; aesop
  suffices: m 0 = m' 0 ∧ (m 0 = m' 0 → z = z' ∧ Fin.tail m = Fin.tail m')
  · constructor <;> try tauto
    have eq_tails : Fin.tail m = Fin.tail m' := by tauto
    apply tuple_eqE_by_cons <;> tauto
  have eq1_w : w = 1 := by
    apply pauli_distinct'' at HHeads
    rw [inv_eq_one] at HHeads; assumption
  subst eq1_w
  constructor
  · simp at HHeads
    assumption
  intro eq_m0
  apply ih
  apply unitary_ext
  rw [HTails]; simp

def fold : pgroup_phases × (Fin n → Pauli) ↪ 𝐔ₙ[n] :=
  ⟨λ zm => fold_aux zm.1 zm.2, by
    rw [Injective]
    intros mp mp' eq_folds
    cases mp with | mk m p
    cases mp' with | mk m' p'
    apply injective_fold_aux at eq_folds
    simp_all
  ⟩


abbrev factored_Pauli n := pgroup_phases × (Fin n → Pauli)
def factored_Pauli_univ : Finset (factored_Pauli n) := Finset.univ
def PauliGroup (n : ℕ) : Finset 𝐔ₙ[n] := (factored_Pauli_univ).map (@fold n)

lemma mem_fold pm : fold pm ∈ PauliGroup n := by
  unfold PauliGroup
  simp
  rw [factored_Pauli_univ]
  exact Finset.mem_univ _

abbrev foldPauli_toFun (n : ℕ) (pm: factored_Pauli n) : PauliGroup n :=
  ⟨fold pm, mem_fold pm⟩

lemma inj_foldPauli : Injective (foldPauli_toFun n) := by
  rw [Injective]
  intros a a' h
  simp [foldPauli_toFun] at h
  exact h

lemma surj_fold (p : PauliGroup n) :
  exists m z, (p : 𝐔ₙ[n]) = fold (z, m) := by
  rcases p with ⟨pval, mem_p⟩
  rw [PauliGroup] at mem_p
  rw [Finset.mem_map] at mem_p
  rcases mem_p with ⟨a, h, h'⟩
  rcases a with ⟨m', z'⟩
  exists z'
  exists m'
  tauto

lemma surj_foldPauli : Surjective (foldPauli_toFun n) := by
  rw [Surjective]
  intro p
  let h := surj_fold p
  rcases h with ⟨m, z, h'⟩
  exists (z, m)
  aesop

local instance : Nonempty (factored_Pauli n) := by
  refine ⟨⟨?phase, ?paulis⟩⟩
  · exact 1
  · intro r
    exact Pauli_I

def foldPauli : factored_Pauli n ≃ PauliGroup n where
  toFun := foldPauli_toFun n
  invFun := invFun (foldPauli_toFun n)
  left_inv := by
    apply Function.leftInverse_invFun
    apply inj_foldPauli
  right_inv := by
    apply Function.rightInverse_invFun
    apply surj_foldPauli

lemma foldPauli_iter (z : pgroup_phases) (m : Fin n → Pauli) (t : Pauli) :
  (foldPauli (z, (Fin.cons t m))).1 = (foldPauli (z, m)) ⊗ₙ t := by
  simp [foldPauli, fold, fold_aux]
  rw [unitary_n_nkron.eq_def]; simp
  rw [<- uphase_of_kron]
  rfl

lemma fold_pauli_mul (p p' : pgroup_phases) (m : Fin n → Pauli) :
  foldPauli ((p * p'), m) = U_phase (foldPauli (p, m)).1 p' := by
  simp [foldPauli, fold, fold_aux]
  rw [uphase_of_uphase]
  aesop

lemma uphase_of_kron' {n₁ n₂} (z : phase) (m1 : 𝐔ₙ[n₁]) (m2 : 𝐔ₙ[n₂]) :
  m1 ⊗ₙ U_phase m2 z = U_phase (m1 ⊗ₙ m2) z := by
  apply unitary_ext
  simp [U_phase, unitary_nkron]
  simp [normalized_kron]
  rw [Matrix.kronecker_smul]
  simp [Matrix.submatrix_smul]

def cast_fin_append {t n₁ n₂} (v₁ : Fin n₁ → t) (v₂ : Fin n₂ → t)
  (i : Fin (n₂ + n₁)) : t :=
  (Fin.append v₁ v₂) (Fin.cast (by group) i)

lemma cast_fin_append_aux {t n₁ n₂}
  (head : t) (tail : Fin n₁ → t) (m : Fin n₂ → t)
  (i : Fin (n₂ + n₁ + 1)) :
  Fin.append (Fin.cons head tail) m (Fin.cast (by ring) i) =
  Fin.cons (α := fun _ => t) head (cast_fin_append tail m) i := by
  unfold cast_fin_append
  simp [Fin.append, Fin.addCases]
  rcases i with _ | i'
  · simp
    rfl
  simp [Fin.cons]

lemma cast_fin_append_iter1 {t n₁ n₂} (m₁ : Fin (n₁ + 1) -> t) (m₂ : Fin n₂ -> t) :
  (cast_fin_append m₁ m₂) = Fin.cons (m₁ 0) (cast_fin_append (Fin.tail m₁) m₂) := by
  unfold cast_fin_append
  ext a
  rcases a with _ | a₀
  · simp [Fin.append, Fin.addCases, Fin.castLT]
  by_cases H: (a₀ < n₁)
  · simp [Fin.append, Fin.addCases, Fin.castLT]
    rw [dif_pos] <;> try assumption
    simp [Fin.cons]
    rw [dif_pos] <;> try assumption
    simp [Fin.tail]
  simp [Fin.append, Fin.addCases, Fin.castLT]
  rw [dif_neg] <;> try assumption
  simp [Fin.cons]
  intro H
  contradiction

lemma cast_fin_append_iter2 {t n₂} (m₁ : Fin 0 -> t) (m₂ : Fin (n₂ + 1) -> t) :
  (cast_fin_append m₁ m₂) = Fin.cons (m₂ 0) (cast_fin_append m₁ (Fin.tail m₂)) := by
  unfold cast_fin_append
  ext a
  rcases a with _ | a₀
  · simp [Fin.append, Fin.addCases]
  simp [Fin.append, Fin.addCases]

lemma kron_Paulis_aux' {n₁ n₂} (z z' : pgroup_phases) (m : Fin n₁ → Pauli)
 (m' : Fin n₂ → Pauli) :
  (foldPauli (z, m)).1 ⊗ₙ (foldPauli (z', m')).1 =
  (foldPauli (z * z', cast_fin_append m' m)).1 := by
  rcases n₂ with _ | n'
  · simp [foldPauli]
    nth_rewrite 2 [fold]
    simp [fold_aux, unitary_n_nkron]
    rw [←@U_phase_id _ _ _ (fold (z, m)), U_phase_tensor, unitary_nkron_zero_id_right]
    simp [fold, fold_aux, U_phase, smul_smul, mul_comm]
    congr
    unfold cast_fin_append
    simp [Fin.append_left_nil]
  induction n' with
  | zero =>
    have: (foldPauli (z', m')).1 = U_phase (m' 0) z' := by
      simp [foldPauli, fold, fold_aux, unitary_n_nkron]
    rw [this]
    rw [fold_pauli_mul]
    rw [uphase_of_kron']
    rw [<- foldPauli_iter]
    suffices: Fin.cons (m' 0) m = cast_fin_append m' m
    · simp [this]
    -- extensionality of fin and whatnot?
    apply funext; intro i
    rw [cast_fin_append]
    rcases i with _ | i'
    · simp [Fin.append, Fin.addCases]
      aesop
    · simp [Fin.append, Fin.addCases]
      aesop
  | succ n'' ih =>
    let m_eq := (Fin.consEquiv (fun _ => Pauli)).symm m'
    let head : Pauli := m_eq.1
    let tail : Fin (n'' + 1) → Pauli := m_eq.2
    -- ???
    have: m' = Fin.cons head tail := by aesop
    rw [this]
    rw [foldPauli_iter]
    simp
    suffices: cast_fin_append (Fin.cons head tail) m =
      Fin.cons (α := fun _ => Pauli) head (cast_fin_append tail m)
    · rw [this]
      clear this
      rw [<- heq_iff_eq]
      apply HEq.trans
      · apply HEq.symm
        apply kron_assoc
      rw [ih]
      rw [<- foldPauli_iter]
      simp only [pgp_mul_eq, Phase.phase_mul_eq, heq_eq_eq]
      try rfl
    -- TODO more fin extensionalities...
    apply funext; intro i
    rw [cast_fin_append]
    rw [cast_fin_append_aux]

def factored_kron {n₁ n₂} (p: factored_Pauli n₁) (p': factored_Pauli n₂) :
  factored_Pauli (n₁ + n₂) :=
  let (z, m) := p
  let (z', m') := p'
  (z * z', cast_fin_append m' m)

lemma kron_PaulisE {n₁ n₂ : ℕ}
  (p : PauliGroup n₁) (p': PauliGroup n₂) :
  p.1 ⊗ₙ p'.1 =
  (foldPauli (factored_kron (foldPauli.symm p) (foldPauli.symm p'))) := by
  let p₀ := foldPauli.symm p
  let p₀' := foldPauli.symm p'
  have: p = foldPauli p₀ := by
    rw [Equiv.apply_symm_apply]
  rw [this]
  have: p' = foldPauli p₀' := by
    rw [Equiv.apply_symm_apply]
  rw [this]
  rw [kron_Paulis_aux']
  rw [factored_kron]
  aesop

lemma cast_split_cat {n₁ n₂ t} (ab : Fin (n₁ + n₂) → t) :
  let cab (i : Fin (n₂ + n₁)) := ab (Fin.cast (by ring) i)
  let abe := (Fin.appendEquiv n₂ n₁).symm cab
  ab = cast_fin_append (abe.1) (abe.2) := by
  unfold cast_fin_append
  intro cab abe
  have: Fin.append abe.1 abe.2 = (Fin.appendEquiv n₂ n₁) abe := by rfl
  rw [this]
  rw [Equiv.apply_symm_apply]
  aesop

lemma kron_mem_PauliGroup {n₁ n₂ : ℕ}
  (U : PauliGroup (n₁ + n₂)) :
  ∃ (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂),
  U.1 = U₁ ⊗ₙ U₂ := by
  let factors := foldPauli.symm U
  let ab := factors.2
  let cab (i : Fin (n₂ + n₁)) := ab (Fin.cast (by rw [add_comm]) i)
  let abe := (Fin.appendEquiv n₂ n₁).symm cab
  let a := abe.1
  let b := abe.2
  exists foldPauli (factors.1, b)
  exists foldPauli (1, a)
  rw [kron_PaulisE]
  simp [factored_kron]
  apply foldPauli.symm.injective
  rw [<- cast_split_cat]
  rw [foldPauli.symm_apply_apply]

lemma PauliGroup_mem_kron {n₁ n₂ : ℕ}
  (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂) :
  U₁ ⊗ₙ U₂ ∈ PauliGroup (n₁+n₂)
  := by
  rw [kron_PaulisE]
  simp

def kronOfPauli {n₁ n₂ : ℕ}
  (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂) :
  PauliGroup (n₁ + n₂) :=
  ⟨U₁ ⊗ₙ U₂, PauliGroup_mem_kron U₁ U₂⟩

theorem kron_mem_PauliGroup_iff {n₁ n₂ : ℕ}
  (U : 𝐔ₙ[n₁ + n₂]) :
  (U ∈ PauliGroup (n₁+n₂)) ↔
  (∃ (U₁ : PauliGroup n₁) (U₂ : PauliGroup n₂), U = U₁ ⊗ₙ U₂) := by
  constructor
  · intro H
    have H' := kron_mem_PauliGroup ⟨U, H⟩
    rcases H' with ⟨U1, U2, H''⟩
    exists U1
    exists U2
  · intro H
    rcases H with ⟨U1, U2, H'⟩
    subst H'
    apply PauliGroup_mem_kron

def unfolded1 := (pgphase_1, (fun (_ : Fin n) => Pauli_I))

lemma kron_of_1s {n₁ n₂} :
  (1 : 𝐔ₙ[n₁]) ⊗ₙ (1 : 𝐔ₙ[n₂]) = 1 := by
  simp [unitary_nkron, normalized_kron, normalize_mat]

lemma foldPauli1 : @fold n unfolded1 = 1 := by
  induction n with
  | zero =>
    simp [fold, fold_aux, unfolded1, unitary_n_nkron, U_phase, Pauli_I]
  | succ n' H =>

    simp [fold, fold_aux, unfolded1]
    simp [unitary_n_nkron]
    rw [<- uphase_of_kron]
    simp [fold, fold_aux, unfolded1] at H
    rw [H]
    have: Pauli_I = (1 : 𝐔ₙ[1]) := by rfl
    rw [this, kron_of_1s]

lemma mem_PauliGroup_id : 1 ∈ PauliGroup n := by
  rw [PauliGroup, Finset.mem_map, factored_Pauli_univ]
  exists unfolded1
  constructor
  · simp only [pgroup_phases, unfolded1, pgphase_1, phase_id]
    exact Finset.mem_univ _

  · apply foldPauli1

def Pauli1 : PauliGroup n := ⟨1, mem_PauliGroup_id⟩

lemma Pauli1_unfold : Pauli1 = foldPauli (pgphase_1, (fun (_ : Fin n) => Pauli_I)) := by
  unfold Pauli1; simp_rw [<- foldPauli1]
  simp [foldPauli, foldPauli_toFun, unfolded1]

def PauliGroup.map (P : PauliGroup n) : (Fin n → Pauli) :=
  (foldPauli.symm P).2

def PauliGroup.phase (P : PauliGroup n) : pgroup_phases :=
  (foldPauli.symm P).1

def PauliGroup.normalized (P : PauliGroup n) := PauliGroup.phase P = pgphase_1

-- trivial now, could possibly delete
lemma rep_unique (f₁ f₂ : factored_Pauli n) (H: foldPauli f₁ = foldPauli f₂) :
  f₁ = f₂ := by
  apply foldPauli.injective
  trivial

lemma map_kron_of_Pauli {n₁ n₂} -- (hn₁ : n₁ > 0) (hn₂ : n₂ > 0)
  (P₁ : PauliGroup n₁) (P₂ : PauliGroup n₂) :
  PauliGroup.map (kronOfPauli P₁ P₂) =
  cast_fin_append (PauliGroup.map P₂) (PauliGroup.map P₁) := by
  let P₁f := foldPauli.symm P₁
  let w₁ := P₁f.1
  let m₁ := P₁f.2
  let P₂f := foldPauli.symm P₂
  let w₂ := P₂f.1
  let m₂ := P₂f.2
  rw [kronOfPauli]
  simp_rw [kron_PaulisE]
  simp [factored_kron, PauliGroup.map]

lemma foldPauli_phase_map {n : ℕ} (P : PauliGroup n) :
    (foldPauli (PauliGroup.phase P, PauliGroup.map P) : PauliGroup n) = P := by
  unfold PauliGroup.phase PauliGroup.map; aesop;
