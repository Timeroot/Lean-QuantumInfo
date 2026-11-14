--i m p o r t QuantumInfo.Finite.Unitary
--i m p o r t QuantumInfo.Finite.Qubit.Basic
import LeanQEC.QuantumInfoSkeleton

import LeanQEC.States.BitVec
import LeanQEC.LinearAlgebra.KroneckerLemmas
import LeanQEC.States.Phase
import LeanQEC.AI_Generated.TediousLinearAlgebra
import LeanQEC.AI_Generated.ne0_unitary

open Matrix

section unitary

theorem reindex_unitary {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
  (e : a ≃ b) (U : 𝐔[a]) : (reindex e e) U.1 ∈ unitaryGroup b ℂ := by
  have h_mem := U.2
  rw [mem_unitaryGroup_iff] at h_mem ⊢
  simp
  rw [star_eq_conjTranspose, conjTranspose_submatrix]
  simp [←star_eq_conjTranspose, h_mem]

def unitary_fin_equiv {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (h: a ≃ b) :(𝐔[a] ≃ 𝐔[b]) where
  toFun U := ⟨(reindex h h) U.1, reindex_unitary _ _⟩
  invFun U := ⟨(Matrix.reindex h.symm h.symm) U.1, reindex_unitary _ _⟩
  left_inv := by
    intro U
    simp
  right_inv := by
    intro U
    simp

notation "𝐔ₙ[" n "]" => Matrix.unitaryGroup (BitVec n) ℂ

open Kronecker in
theorem nkron_unitary {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) : normalized_kron a.val b.val ∈ 𝐔ₙ[n₁ + n₂] := by
  rw [normalized_kron, normalize_mat]
  exact reindex_unitary bits_cat ⟨_, kron_unitary a b⟩

open Kronecker in
def unitary_nkron {n₁ n₂ : ℕ} (a : 𝐔ₙ[n₁]) (b : 𝐔ₙ[n₂]) : 𝐔ₙ[n₁ + n₂] := ⟨_, nkron_unitary a b⟩

notation a:60 " ⊗ₙ " b:60 => unitary_nkron a b

noncomputable def unitary_n_nkron {n : ℕ} (m : Fin n → 𝐔ₙ[1]) : 𝐔ₙ[n] :=
match n with
| 0 => 1
| n₀+1 => (unitary_nkron (unitary_n_nkron (λ (x : Fin n₀) => m ⟨x.val + 1, by simp [x.isLt]⟩)) (m 0))


def unitaries_cat {l₁ l₂ n : ℕ} (m₁ : Fin l₁ → 𝐔ₙ[n]) (m₂ : Fin l₂ → 𝐔ₙ[n]) : Fin (l₁ + l₂) → 𝐔ₙ[n] :=
  fun x => if hle : x < l₁ then (m₁ ⟨x.1, hle⟩)
  else (m₂ ⟨x.1 - l₁, by push_neg at hle; apply Nat.sub_lt_right_of_lt_add hle; simp_rw [add_comm]; exact x.2⟩)

/-
theorem unitaries_cat_nkron {l₁ l₂} (m₁ : Fin l₁ → 𝐔ₙ[1]) (m₂ : Fin l₂ → 𝐔ₙ[1]) :
  (unitary_n_nkron m₁) ⊗ₙ (unitary_n_nkron m₂) = unitary_n_nkron (unitaries_cat m₁ m₂) := by
  aesop
  -/

lemma normalize_dagger {a₁ b₁ a₂ b₂}
  (m : Matrix (BitVec a₁ × BitVec b₁) (BitVec a₂ × BitVec b₂) ℂ):
  (normalize_mat m)ᴴ = normalize_mat mᴴ := by
  rw [normalize_mat, normalize_mat]
  rw [conjTranspose_reindex]

--maybe unitary_nkron should have an underlying version using matrices?
lemma unitary_herm_of_kron_herm {n₁ n₂ : ℕ} {M₁ : 𝐔ₙ[n₁]} {M₂ : 𝐔ₙ[n₂]} (hM₁ : M₁.val.IsHermitian) (hM₂ : M₂.val.IsHermitian) :
  Matrix.IsHermitian (M₁ ⊗ₙ M₂).val := by
  simp [IsHermitian, unitary_nkron]
  rw [normalized_kron, kronecker, normalize_dagger]
  rw [Matrix.conjTranspose_kronecker]
  rw [hM₁, hM₂]

def herm_of_qubit_tensor_herm {n : ℕ} (m : Fin n → 𝐔ₙ[1]) (Hm : ∀ x, Matrix.IsHermitian (m x).1) :
  Matrix.IsHermitian (unitary_n_nkron m).1 := by
  induction n with
  | zero => exact Matrix.isHermitian_one
  | succ n ih => rw [unitary_n_nkron]
                 apply unitary_herm_of_kron_herm (ih _ _) (Hm 0)
                 exact fun x => (Hm ⟨x+1, by norm_num⟩)

noncomputable section

def U_phase {k : Type*} [Fintype k] [DecidableEq k] (U : 𝐔[k]) (z : phase) : 𝐔[k] := ⟨z.1 • U.val, by
  simp [Unitary.mem_iff, smul_smul, mul_comm]
  rw [mul_comm, ←Complex.normSq_eq_conj_mul_self, Complex.coe_smul, Complex.normSq_eq_norm_sq, z.2]
  simp
⟩

@[simp]
lemma U_phase_id {k : Type*} [Fintype k] [DecidableEq k] {U : 𝐔[k]} : U_phase U phase_id = U := by
  simp [U_phase, phase_id]


def phase.unitary_of (z : phase) (n : ℕ) : 𝐔ₙ[n] := U_phase 1 z

lemma U_phase_tensor {n₁ n₂ : ℕ} (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) (z₁ z₂ : phase) :
  (U_phase U₁ z₁) ⊗ₙ (U_phase U₂ z₂) = U_phase (U₁ ⊗ₙ U₂) (z₁ * z₂) := by
  simp [U_phase, unitary_nkron, normalized_kron, kroneckerMap]
  ext i j; simp; ring

def u_neg {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[n] := (U_phase U ⟨-1, by norm_num⟩)

def u_im {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[n] := (U_phase U ⟨Complex.I, by norm_num⟩)

def fin2prodbitvec_equiv {n : ℕ} : (Fin 2 × BitVec n) ≃ BitVec (1+n) := (beq.prodCongr (Equiv.refl _)).trans bits_cat

def n_controllize {n : ℕ} (U : 𝐔ₙ[n]) : 𝐔ₙ[1+n] := unitary_fin_equiv fin2prodbitvec_equiv (Qubit.controllize U)

notation "Cₙ[" g "]" => n_controllize g

lemma unitary_ext {n} {U U' : 𝐔ₙ[n]} (vals_eq: U.1 = U'.1) : U = U' := by aesop

lemma unitary_nkron_valE {n₁ n₂}
  (M₁ : 𝐔ₙ[n₁]) (M₂ : 𝐔ₙ[n₂]) :
  (M₁ ⊗ₙ M₂).1 = normalize_mat (Matrix.kronecker M₁ M₂)
  := by simp [unitary_nkron, normalized_kron]

lemma uphase_of_kron {n₁ n₂} (z : phase) (m1 : 𝐔ₙ[n₁]) (m2 : 𝐔ₙ[n₂]) :
  U_phase m1 z ⊗ₙ m2 = U_phase (m1 ⊗ₙ m2) z := by
  apply unitary_ext
  simp [U_phase, unitary_nkron]
  simp [normalized_kron]
  simp [Matrix.smul_kronecker, Matrix.submatrix_smul]

lemma uphase_div {n} (z z' : phase) (u u' : 𝐔ₙ[n])
  (eq : U_phase u z = U_phase u' z') :
  let r := z * Phase.phase_star z'
  U_phase u r = u' := by
  apply unitary_ext
  simp [U_phase, Phase.phase_star] at ⊢ eq
  apply raw_uphase_div; try assumption
  rcases z' with ⟨zval, znorm⟩
  simp_all; assumption

lemma u_phase_eq_is_1 {n} {z : phase} {u : 𝐔ₙ[n]}
  (eq : U_phase u z = u) :
  z = phase_id := by
  cases z with | mk zval z_norm
  rw [U_phase] at eq
  cases u with | mk uval unitary_u
  simp_all
  apply raw_uphase_eq_is_1 at eq
  · assumption
  apply ne0_unitary
  aesop

lemma uphase_eqE {n} (s s' : phase) (U U' : 𝐔ₙ[n])
  (eq: U_phase U s = U_phase U' s') :
  s.1 • U.val = s'.1 • U'.val := by
  simp [U_phase] at eq
  assumption

lemma uphase_of_uphase (U : 𝐔ₙ[n]) z z' :
  U_phase (U_phase U z) z' = U_phase U (z * z') := by
  simp [U_phase]
  module

lemma mul_unitary_n_nkrons {n} (U₁ : Fin n -> 𝐔ₙ[1]) (U₂ : Fin n -> 𝐔ₙ[1]) :
  unitary_n_nkron (λ i => (U₁ i) * (U₂ i)) =
  (unitary_n_nkron U₁) * (unitary_n_nkron U₂) := by
  induction n with
  | zero =>
    simp [unitary_n_nkron]
  | succ n₀ IH =>
    simp [unitary_n_nkron, unitary_nkron, normalized_kron, Matrix.kronecker]
    rw [<- Matrix.mul_kronecker_mul]
    aesop

lemma mul_Uphases {n} (z₁ z₂) (U₁ U₂ : 𝐔ₙ[n]) :
  U_phase (U₁ * U₂) (z₁ * z₂) = U_phase U₁ z₁ * U_phase U₂ z₂ := by
  simp [U_phase]; module
