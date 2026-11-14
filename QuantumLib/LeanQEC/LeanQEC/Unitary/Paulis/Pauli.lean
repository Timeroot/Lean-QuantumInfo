import LeanQEC.Unitary.Basic
import LeanQEC.States.Phase
import LeanQEC.AI_Generated.ne0_unitary
import LeanQEC.AI_Generated.scalar_mat_is_one
import LeanQEC.AI_Generated.KronNonsense
import LeanQEC.AI_Generated.PauliBruteForce
-- import LeanQEC.AI_Generated.TediousLinearAlgebra
import LeanQEC.Unitary.Paulis.Pauli1
import LeanQEC.Unitary.Paulis.PauliFolding
import LeanQEC.Unitary.Paulis.PauliMul
import LeanQEC.Unitary.Paulis.PauliCommute

open Qubit
open Function

noncomputable section

-- variable {l : ℕ} (m_test : Fin l → Pauli)
variable {n : ℕ} (m : Fin n → Pauli)

def normalize_pauli (U : PauliGroup n) : PauliGroup n :=
  (foldPauli (pgphase_1, (PauliGroup.map U)))

lemma normalize_pauli_idem (U : PauliGroup n) : normalize_pauli (normalize_pauli U) = normalize_pauli U := by
  simp [normalize_pauli, PauliGroup.map]

lemma normalize_pauli_map_eq (U : PauliGroup n) : PauliGroup.map U = PauliGroup.map (normalize_pauli U) := by
  simp [normalize_pauli, PauliGroup.map]

def pauli_weight (U : PauliGroup n) : ℕ :=
  (Finset.univ.filter (fun i => (PauliGroup.map U) i ≠ Pauli_I)).card

def pauli_only (U : PauliGroup n) (P : Pauli) :=
  ∀ x, ((PauliGroup.map U) x = Pauli_I ∨ (PauliGroup.map U) x = P)

def pauli_pauli_phase (U₁ U₂ : PauliGroup n) : pgroup_phases :=
  if anticommute U₁ U₂ then pgphase_n1 else pgphase_1

lemma pauli_pauli_phase_kron {n₁ n₂ : ℕ}
  (U₁ U₁' : PauliGroup n₁)
  (U₂ U₂' : PauliGroup n₂) :
  (pauli_pauli_phase U₁ U₁') * (pauli_pauli_phase U₂ U₂') =
  (pauli_pauli_phase
    (kronOfPauli U₁ U₂)) (kronOfPauli U₁' U₂') := by
  unfold pauli_pauli_phase
  rw [anticommute_kron]
  rcases (anticommute U₁ U₁') with Ht | Hf
  all_goals rcases (anticommute U₂ U₂') with Ht₂ | Hf₂
  all_goals simp

lemma pauli_pauli_phase_symm (P₁ P₂ : PauliGroup n) :
  pauli_pauli_phase P₁ P₂ = pauli_pauli_phase P₂ P₁ := by
  unfold pauli_pauli_phase
  rw [anticommute_sym]

lemma pauli_pauli_phase_self (U : PauliGroup n) :
  pauli_pauli_phase U U = pgphase_1 := by
  simp [pauli_pauli_phase, anticommute_xx]

def pgX := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_X)
def pgY := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_Y)
def pgZ := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_Z)
def pg1 := foldPauli (pgphase_1, fun (_ : Fin 1) => Pauli_I)

@[simp]
lemma pphase_XZ : pauli_pauli_phase pgX pgZ = pgphase_n1 := by
  simp only [pauli_pauli_phase]
  simp only [anticommute]
  simp only [anticommuteₘ]
  suffices: !(commute₁ (PauliGroup.map pgX 0) (PauliGroup.map pgZ 0))
  · simp_rw [this]
    simp
  simp [commute₁, PauliGroup.map, pgX, pgZ]

@[simp]
lemma pphase_ZX : pauli_pauli_phase pgZ pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XZ

@[simp]
lemma pphase_XY : pauli_pauli_phase pgX pgY = pgphase_n1 := by
  simp only [pauli_pauli_phase]
  simp only [anticommute]
  simp only [anticommuteₘ]
  suffices: !(commute₁ (PauliGroup.map pgX 0) (PauliGroup.map pgY 0))
  · simp_rw [this]
    simp
  simp [commute₁, PauliGroup.map, pgX, pgY]

@[simp]
lemma pphase_YX : pauli_pauli_phase pgY pgX = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_XY

@[simp]
lemma pphase_YZ : pauli_pauli_phase pgY pgZ = pgphase_n1 := by
  simp only [pauli_pauli_phase]
  simp only [anticommute]
  simp only [anticommuteₘ]
  suffices: !(commute₁ (PauliGroup.map pgY 0) (PauliGroup.map pgZ 0))
  · simp_rw [this]
    simp
  simp [commute₁, PauliGroup.map, pgZ, pgY]

@[simp]
lemma pphase_ZY : pauli_pauli_phase pgZ pgY = pgphase_n1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_YZ

@[simp]
lemma pphase_id_right {U : PauliGroup 1} :
  pauli_pauli_phase pg1 U = pgphase_1 := by
  simp only [pauli_pauli_phase]
  simp only [anticommute, anticommuteₘ]
  have: PauliGroup.map pg1 0 = Pauli_I := by
    simp [PauliGroup.map, pg1]
  simp_rw [this]
  simp [commute₁]

@[simp]
lemma pphase_id_left (U : PauliGroup 1) :
  pauli_pauli_phase U pg1 = pgphase_1 := by
  rw [pauli_pauli_phase_symm]
  exact pphase_id_right

lemma pauli_mul' {n : ℕ} (U₁ U₂ : PauliGroup n) :
  U₁.val * U₂.val ∈ PauliGroup n := by
  rw [<- mul_Paulis_correct]
  aesop

lemma pauli_mul {n : ℕ} {U₁ U₂ : 𝐔ₙ[n]}
 (hP₁ : U₁ ∈ PauliGroup n) (hP₂ : U₂ ∈ PauliGroup n) :
 U₁ * U₂ ∈ PauliGroup n := by
 apply (pauli_mul' ⟨U₁, hP₁⟩ ⟨U₂, hP₂⟩)

def factored_inv {n : ℕ} (U : factored_Pauli n) : factored_Pauli n :=
  (pgroup_phases.inv U.1, U.2)

lemma scale1_factored_Pauli {n} (P : factored_Pauli n) :
  scale_factored_Pauli pgphase_1 P = P := by
  rw [scale_factored_Pauli]
  have: pgphase_1 = 1 := by rfl
  rw [this]
  rw [PauliPhases.one_mul]

lemma factored_inv_correct {n} (U : factored_Pauli n) :
  foldPauli (factored_inv U) = ((foldPauli U).val)⁻¹ := by
  symm; rw [DivisionMonoid.inv_eq_of_mul]
  rw [<-mul_Paulis_correct]
  simp [factored_inv, mul_Paulis]
  simp [mul_factored_Paulis]
  have: (U.1).val.z * ((pgroup_phases.inv U.1)).val.z = 1 := by
    suffices: U.1 * pgroup_phases.inv U.1 = 1
    · have H := congrArg (λx => x.val.z) this
      simp at H
      rw [H]
      rfl
    apply mul_inv_cancel
  simp_rw [this]
  conv =>
    enter[1]
    enter[1]
    enter[2]
    enter[1]
    change pgphase_1
  rw [scale1_factored_Pauli]
  rw [mul_Pauli1_tuples_xx]
  rw [unfolded1]
  rw [<- Pauli1_unfold]
  rfl

lemma pauli_inv' {n : ℕ} (U: PauliGroup n) :
  (U.val)⁻¹ ∈ PauliGroup n := by
  let FU := foldPauli.symm U
  have: U = foldPauli FU := by aesop
  rw [this]
  rw [<- factored_inv_correct]
  aesop

lemma pauli_inv {n : ℕ} {U : 𝐔ₙ[n]} (hU : U ∈ PauliGroup n)
  : U⁻¹ ∈ PauliGroup n := by
  apply (pauli_inv' ⟨U, hU⟩)

--we don't seem to get much from this...
instance PauliGroup_group (n : ℕ) : Subgroup 𝐔ₙ[n] where
  carrier := PauliGroup n
  mul_mem' := by intros a b ha hb; apply pauli_mul ha hb
  one_mem' := mem_PauliGroup_id
  inv_mem' := by intros x hx; apply pauli_inv hx

lemma pauli_commute_or_anticommute' {n} (P Q : PauliGroup n) :
  P.val * Q.val = Q.val * P.val ∨
  P.val * Q.val = - Q.val * P.val := by
  by_cases H: anticommute P Q
  · right
    apply anticommute_correct_true; assumption
  · left
    apply anticommute_correct_false
    simp_all [Bool.not_eq_true]

lemma anticommute_iff_normalize_anticommute {n : ℕ} (P Q : PauliGroup n)
 : anticommute P Q ↔ anticommute (normalize_pauli P) Q := by
  unfold anticommute
  rw [normalize_pauli_map_eq Q]
  nth_rw 1 [normalize_pauli_map_eq P]

lemma pauli_commute_or_anticommute {n : ℕ}{U₁ U₂ : 𝐔ₙ[n]}
  (hU₁ : U₁ ∈ PauliGroup n) (hU₂ : U₂ ∈ PauliGroup n) :
  U₁ * U₂ = U₂ * U₁ ∨ U₁ * U₂ = - U₂ * U₁ := by
  apply (pauli_commute_or_anticommute' ⟨U₁, hU₁⟩ ⟨U₂, hU₂⟩)

