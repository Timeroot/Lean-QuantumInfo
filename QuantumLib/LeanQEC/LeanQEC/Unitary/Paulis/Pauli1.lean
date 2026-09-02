-- Single-qubit Paulis

import LeanQEC.Unitary.Basic
import LeanQEC.States.Phase
import LeanQEC.AI_Generated.ne0_unitary
import LeanQEC.AI_Generated.scalar_mat_is_one
import LeanQEC.AI_Generated.KronNonsense
import LeanQEC.AI_Generated.PauliBruteForce

open Qubit
open Function

noncomputable section

def pgroup_phases : Finset phase := {⟨1, by norm_num⟩, ⟨-1, by norm_num⟩, ⟨Complex.I, by norm_num⟩, ⟨-Complex.I, by norm_num⟩}

lemma pgphase_cases (a : pgroup_phases) : a.1 = ⟨1, by norm_num⟩ ∨ a.1 = ⟨-1, by norm_num⟩ ∨
  a.1 = ⟨Complex.I, by norm_num⟩ ∨ a.1 = ⟨-Complex.I, by norm_num⟩ := by
  have:= a.2
  simp only [pgroup_phases, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

@[simp]
def pgphase_1 : pgroup_phases := ⟨phase_id, by simp [pgroup_phases]⟩

@[simp]
def pgphase_n1 : pgroup_phases := ⟨⟨-1, by norm_num⟩, by simp [pgroup_phases]⟩

lemma pgroup_phases_closed_under_mul : ∀ a b : pgroup_phases, a.1 * b.1 ∈ pgroup_phases := by
  intros a b
  rcases (pgphase_cases a) with ha | ha | ha |ha; all_goals rcases (pgphase_cases b) with hb | hb | hb | hb
  all_goals simp [ha, hb, pgroup_phases]

def pgroup_phases.gmul (a b : pgroup_phases) : pgroup_phases := ⟨_, pgroup_phases_closed_under_mul a b⟩

lemma pgroup_phases_closed_under_inv : ∀ a : pgroup_phases, (Phase.phase_star a.1) ∈ pgroup_phases := by
  intros a
  rcases (pgphase_cases a) with ha | ha | ha | ha
  all_goals simp [ha, Phase.phase_star, pgroup_phases]

def pgroup_phases.inv (a : pgroup_phases) : pgroup_phases := ⟨_, pgroup_phases_closed_under_inv a⟩

instance PauliPhases : Group pgroup_phases where
  mul := pgroup_phases.gmul
  mul_assoc := by
    intros a b c
    suffices ((⟨a.1 * b.1 * c.1, pgroup_phases_closed_under_mul ⟨_,
     (pgroup_phases_closed_under_mul _ _)⟩ _⟩ : pgroup_phases) = ⟨a.1 * (b.1 * c.1),
      pgroup_phases_closed_under_mul _ (⟨_, pgroup_phases_closed_under_mul _ _⟩)⟩) by
      exact this
    simp [mul_assoc]
  one := pgphase_1
  one_mul := by
    intros a
    suffices ⟨pgphase_1.1 * a.1, pgroup_phases_closed_under_mul _ _⟩ = a by
      exact this
    simp
  mul_one := by
    intros a
    suffices ⟨a.1 * pgphase_1.1, pgroup_phases_closed_under_mul _ _⟩ = a by
      exact this
    simp
  inv := pgroup_phases.inv
  inv_mul_cancel := by
    intros a
    rw [pgroup_phases.inv]
    suffices ⟨Phase.phase_star a.1 * a.1, pgroup_phases_closed_under_mul ⟨_, (pgroup_phases_closed_under_inv _)⟩ _⟩ = pgphase_1 by
      exact this
    simp [Phase.phase_star]
    rcases (pgphase_cases a) with ha | ha | ha | ha
    all_goals simp [ha]

@[simp]
lemma pgp_mul_eq (p1 : pgroup_phases) (p2 : pgroup_phases) : p1 * p2 = ⟨p1.1 * p2.1, pgroup_phases_closed_under_mul _ _⟩ := by
  rfl

lemma mul_comm_pgroup_phases (a b : pgroup_phases) :
  a * b = b * a := by simp; group

lemma phase_id_coe : (↑(1 : pgroup_phases) : phase).z = 1 := by
  rfl

def pX := (unitary_fin_equiv beq) X
def pY := (unitary_fin_equiv beq) Y
def pZ := (unitary_fin_equiv beq) Z
def p1 : 𝐔ₙ[1] := 1

noncomputable def Pauli : Finset (𝐔ₙ[1]):= {1, pX, pY, pZ}

def Pauli_X : Pauli := ⟨pX, by simp [Pauli]⟩
def Pauli_Y : Pauli := ⟨pY, by simp [Pauli]⟩
def Pauli_Z : Pauli := ⟨pZ, by simp [Pauli]⟩
def Pauli_I : Pauli := ⟨1, by simp [Pauli]⟩

@[simp] lemma pgXnepgI : Pauli_X ≠ Pauli_I := by
  -- To show that Pauli_X ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_X.val 0 0) ≠ (Pauli_I.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgInepgX : Pauli_I ≠ Pauli_X := pgXnepgI.symm

@[simp] lemma pgZnepgI : Pauli_Z ≠ Pauli_I := by
  -- To show that Pauli_Z ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_Z.val 1 1) ≠ (Pauli_I.val 1 1) := by
    exact show ( -1 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgInepgZ : Pauli_I ≠ Pauli_Z := pgZnepgI.symm

@[simp] lemma pgYnepgI : Pauli_Y ≠ Pauli_I := by
  -- To show that Pauli_Y ≠ Pauli_I, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_Y.val 0 0) ≠ (Pauli_I.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgInepgY : Pauli_I ≠ Pauli_Y := pgYnepgI.symm

@[simp] lemma pgXnepgZ : Pauli_X ≠ Pauli_Z := by
  -- To show that Pauli_X ≠ Pauli_Z, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_X.val 0 0) ≠ (Pauli_Z.val 0 0) := by
    exact show ( 0 : ℂ ) ≠ 1 from by norm_num;
  contrapose! h_diff; aesop;

@[simp] lemma pgZnepgX : Pauli_Z ≠ Pauli_X := pgXnepgZ.symm


@[simp] lemma pgXnepgY : Pauli_X ≠ Pauli_Y := by
  -- To show that Pauli_X ≠ Pauli_Y, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_X.val 1 0) ≠ (Pauli_Y.val 1 0) := by
    exact show 1 ≠ Complex.I from by
      intro h
      have := congrArg Complex.im h
      simp at this;
  contrapose! h_diff; aesop;

@[simp] lemma pgYnepgX : Pauli_Y ≠ Pauli_X := pgXnepgY.symm

@[simp] lemma pgZnepgY : Pauli_Z ≠ Pauli_Y := by
  -- To show that Pauli_X ≠ Pauli_Y, we can compare their entries. The (0,0) entry of Pauli_X is 0, while the (0,0) entry of Pauli_I is 1. Since these entries are different, the matrices cannot be equal.
  have h_diff : (Pauli_Z.val 0 0) ≠ (Pauli_Y.val 0 0) := by
    exact show 1 ≠ 0 from by norm_num
  contrapose! h_diff; aesop;

@[simp] lemma pgYnepgZ : Pauli_Y ≠ Pauli_Z := pgZnepgY.symm

lemma Pauli_cases (a : Pauli) :
  a = Pauli_X ∨ a = Pauli_Y ∨ a = Pauli_Z ∨ a = Pauli_I := by
  rcases a with ⟨u, hu⟩
  have: u = 1 ∨ u = pX ∨ u = pY ∨ u = pZ := by
    simpa [Pauli, Finset.mem_insert, Finset.mem_singleton] using hu
  aesop

lemma mem_raw_paulis (u : Pauli) :
  (Matrix.reindex beq.symm beq.symm) u ∈ raw_Paulis := by
  have H := Pauli_cases u
  rcases H with HX | HY | HZ | HI
  · subst HX; simp [Pauli_X, pX, unitary_fin_equiv, X, raw_Paulis]; tauto
  · subst HY; simp [Pauli_Y, pY, unitary_fin_equiv, Y, raw_Paulis]; tauto
  · subst HZ; simp [Pauli_Z, pZ, unitary_fin_equiv, Z, raw_Paulis]; tauto
  · subst HI; simp [Pauli_I, raw_Paulis]; tauto

lemma reindex_symm_hmul (z : ℂ) (p : Matrix (BitVec 1) (BitVec 1) ℂ) :
  (Matrix.reindex beq beq).symm (z • p) = z • (Matrix.reindex beq beq).symm p := by
  aesop

lemma paulis_distinct_aux {p p' : Pauli} (z : ℂ) (H: p ≠ p') :
  z • p.val.1 ≠ p'.val.1 := by
  let rawP : raw_Paulis := ⟨Matrix.reindex beq.symm beq.symm p.val.1, ?_⟩; swap
  · apply mem_raw_paulis
  let rawP' : raw_Paulis := ⟨Matrix.reindex beq.symm beq.symm p'.val.1, ?_⟩; swap
  · apply mem_raw_paulis
  suffices: z • rawP.1 ≠ rawP'.1
  · by_contra H'
    apply (congrArg (Matrix.reindex beq beq).symm) at H'
    rw [reindex_symm_hmul] at H'
    contradiction
  apply raw_paulis_distinct
  suffices: rawP.val ≠ rawP'.val
  · tauto
  by_contra H'
  apply (congrArg (Matrix.reindex beq beq)) at H'
  aesop

lemma paulis_distinct {p p' : Pauli} (z : pgroup_phases) (H: p ≠ p') :
  (U_phase p.val z) ≠ p' := by
  suffices: z.1.1 • p.val.1 ≠ p'.val.1
  · rw [U_phase]; aesop
  apply paulis_distinct_aux; assumption

lemma pgroup_phases_mul_coe (a b : pgroup_phases) :
  ↑(a * b) = a.1 * b.1 := by
  aesop

-- There's gotta be an easier way...
lemma pgroup_phases_star_move (a b c : pgroup_phases) :
  a * pgroup_phases.inv b = c ↔ a = b * c := by
  suffices: a.1 * Phase.phase_star b.1 = c ↔ a.1 = b.1 * c.1
  · rw [pgroup_phases.inv]
    rcases a with ⟨a0, ha⟩
    rcases b with ⟨b0, hb⟩
    rcases c with ⟨c0, hc⟩
    constructor
    · intro H'
      apply Subtype.ext ?_
      rw [pgroup_phases_mul_coe]
      rw [<- this]
      apply congrArg (fun x => x.1) at H'
      rw [<- H']
      rfl
    · intro H'
      apply Subtype.ext ?_
      rw [pgroup_phases_mul_coe]
      rw [this]
      apply congrArg (fun x => x.1) at H'
      rw [H']
      rfl
  apply phase_star_move

lemma pgphase_id_1 (a : pgroup_phases) :
  a * pgphase_1 = a := by
  rcases a with ⟨a₀, ha⟩
  simp [pgphase_1]

lemma uphase_injective (z z' : pgroup_phases) (p p' : Pauli)
  (eq: U_phase p.val z = U_phase p'.val z') :
  z = z' /\ p = p' := by
  let r := z * pgroup_phases.inv z'
  have eq' : U_phase p.val r = p'.val
  · apply uphase_div; assumption
  suffices: (p = p' → z = z') /\ p = p'
  · tauto
  constructor
  · intro H'; subst H'
    suffices this: r = pgphase_1
    · rw [this] at eq'
      rw [pgroup_phases_star_move, pgphase_id_1] at this
      assumption
    apply u_phase_eq_is_1 at eq'
    aesop
  by_contra H
  let H' := paulis_distinct r H
  contradiction

-- need this thing later too...
-- sigh. looks terrible, I know.
lemma pauli_distinct'' {z : ℂˣ} {m m' : Pauli} (eq: m.val.1 = z • m'.val.1) :
  z = 1 := by
  by_cases H: m = m'
  · subst H
    symm at eq
    apply scalar_mat_is_one at eq
    · simp_all
    apply ne0_unitary
    aesop
  revert eq
  suffices: z ≠ 1 → m.val.1 ≠ z • ↑↑m'
  · tauto
  intro ne1_z
  symm
  apply paulis_distinct_aux
  symm
  assumption

lemma isHermitian_X : Matrix.IsHermitian pX.1 := by
  rw [Matrix.IsHermitian, pX]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.X ]

lemma isHermitian_Y : Matrix.IsHermitian pY.1 := by
  rw [Matrix.IsHermitian, pY]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.Y ]

lemma isHermitian_Z : Matrix.IsHermitian pZ.1 := by
  rw [Matrix.IsHermitian, pZ]
  apply Matrix.ext; intros i j
  rw [Matrix.conjTranspose_apply]
  simp [unitary_fin_equiv, beq]
  simp [BitVec.equivFin]
  rcases i with ⟨ _ | _, _ ⟩ <;> rcases j with ⟨ _ | _, _ ⟩ <;> norm_num [ Qubit.Z ]

lemma pauli_herm {p : Pauli} : Matrix.IsHermitian p.1.1 := by
  rcases p with ⟨x, hx⟩
  rw [Pauli] at hx
  simp at hx ⊢
  rcases hx with (rfl | rfl | rfl | rfl)
  · simp
  · apply isHermitian_X
  · apply isHermitian_Y
  · apply isHermitian_Z
