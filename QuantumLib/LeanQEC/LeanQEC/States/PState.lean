import LeanQEC.States.BitVec
import LeanQEC.Unitary.Basic
import LeanQEC.Braket

section pstate

abbrev PState (n : ℕ) := BitVec n → ℂ

variable {n : ℕ}

theorem unitary_inner_preserve {k : Type*} [Fintype k] [DecidableEq k] (v₁ v₂ : k → ℂ) (U : 𝐔[k]) :
  ∑ x : k, (U.val.mulVec v₁) x * starRingEnd ℂ ((U.val.mulVec v₂) x) = ∑ x : k, v₁ x * starRingEnd ℂ (v₂ x) := by
  have h_unitary : U.val.conjTranspose * U.val = 1 := by
    rw [←Matrix.star_eq_conjTranspose, ←Matrix.mem_unitaryGroup_iff']
    simp_all only [SetLike.coe_mem]
  have h_inner : ∑ x : k, (U.val.mulVec v₁) x * starRingEnd ℂ ((U.val.mulVec v₂) x) = ∑ x : k, ∑ y : k, v₁ y * starRingEnd ℂ (v₂ x) * (U.val.conjTranspose * U.val) x y := by
    simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
    simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm )
  rw [h_inner]
  simp_all [Matrix.one_apply]

noncomputable section

@[simp]
def PState.apply (ψ : PState n) (U : 𝐔ₙ[n]) : PState n := U.1.toLin' ψ

def PState.kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) : PState (n₁ + n₂) :=
  ket_prod ψ₁ ψ₂

notation a:60 " ⊗ₚ " b:60 => PState.kron a b

open scoped unitary

theorem kron_mul_kron {n₁ n₂ : ℕ} (ψ₁ : PState n₁) (ψ₂ : PState n₂) (U₁ : 𝐔ₙ[n₁]) (U₂ : 𝐔ₙ[n₂]) :
  (ψ₁ ⊗ₚ ψ₂).apply (U₁ ⊗ₙ U₂) = (ψ₁.apply U₁) ⊗ₚ (ψ₂.apply U₂) := by
  simp [PState.kron, unitary_nkron, kron_prod]

/-
The trivial pure state, on 0 qubits, or a vector space with dimension 1.
-/
def PState.trivial : PState 0 := fun _ => 1

def pstate_n_kron {n : ℕ} (m : Fin n → PState 1) : PState n :=
match n with
| 0 => PState.trivial
| n₀+1 => ((pstate_n_kron (λ (x : Fin n₀) => m ⟨x.val + 1, by simp [x.isLt]⟩)).kron (m 0))

lemma PState.kron_val (n₁ n₂) {ψ₁ : PState n₁} {ψ₂ : PState n₂} {x : BitVec (n₁ + n₂)} :
  (ψ₁ ⊗ₚ ψ₂) x = (ψ₁ (bits_cat.symm x).1) * (ψ₂ (bits_cat.symm x).2) := by
  simp [PState.kron, ket_prod, toMat, normalized_kron]

lemma PState.kron_assoc {ψ₁ ψ₂ ψ₃ : PState 1} : (ψ₁ ⊗ₚ ψ₂) ⊗ₚ ψ₃ = ψ₁ ⊗ₚ (ψ₂ ⊗ₚ ψ₃) := by
  ext x
  rw [@PState.kron_val 2 1, PState.kron_val]
  rw [@PState.kron_val 1 2, PState.kron_val]
  rw [mul_assoc]
  fin_cases x <;> rfl

open ComplexConjugate

@[simp]
def PState.dot {n : ℕ} (ψ₁ ψ₂ : PState n) : ℂ := ψ₁ ⬝ᵥ (conj ψ₂)

lemma PState.dot_star_symm {n : ℕ} (ψ₁ ψ₂ : PState n) : ψ₁.dot ψ₂ = conj (ψ₂.dot ψ₁) := by
  unfold PState.dot dotProduct
  simp_rw [starRingEnd_apply, star_sum, star_mul]
  simp

@[simp]
lemma starRingEnd_smul {R : Type u} [CommSemiring R] [StarRing R]
  {A : Type v} [CommSemiring A] [StarRing A] [SMul R A] [StarModule R A] (x : R) (y : A)
   : (starRingEnd A) (x • y) = ((starRingEnd R) x) • ((starRingEnd A) y) := by
  rw [starRingEnd_apply, star_smul, ←starRingEnd_apply, ←starRingEnd_apply]

@[simp]
def PState.orth {n : ℕ} (ψ₁ ψ₂ : PState n) : Prop := ψ₁.dot ψ₂ = 0

lemma PState.orth_symm {n : ℕ} {ψ₁ ψ₂ : PState n} :
  ψ₁.orth ψ₂ ↔ ψ₂.orth ψ₁ := by
  unfold PState.orth
  rw [PState.dot_star_symm]
  simp

@[simp]
lemma PState.dot_orth1 {n : ℕ} {ψ₁ ψ₂ : PState n} (h_orth : ψ₁.orth ψ₂) :
  ψ₁ ⬝ᵥ starRingEnd (BitVec n → ℂ) ψ₂ = 0 := h_orth

@[simp]
lemma PState.dot_orth2 {n : ℕ} {ψ₁ ψ₂ : PState n} (h_orth : ψ₁.orth ψ₂) :
  ψ₂ ⬝ᵥ starRingEnd (BitVec n → ℂ) ψ₁ = 0 := PState.orth_symm.1 h_orth

lemma PState.apply_eq {n : ℕ} {ψ : PState n} {U : 𝐔ₙ[n]} {i : BitVec n} : (ψ.apply U) i = (U.val.mulVec ψ) i := by rfl

lemma PState.apply_orth {n : ℕ} {ψ φ : PState n} (h_orth : ψ.orth φ) {U : 𝐔ₙ[n]} :
  (ψ.apply U).orth (φ.apply U) := by
  unfold PState.orth
  have h_dot : PState.dot (ψ.apply U) (φ.apply U) = PState.dot ψ φ := by
    unfold PState.dot dotProduct
    simp_rw [Pi.conj_apply, PState.apply_eq]
    exact unitary_inner_preserve _ _ _
  rw [h_dot]
  exact h_orth

@[simp]
lemma PState.apply_id {n : ℕ} {ψ : PState n} : ψ.apply 1 = ψ := by simp

lemma PState.apply_add {n : ℕ} (ψ φ : PState n) (U : 𝐔ₙ[n]) :
  (ψ + φ).apply U = ψ.apply U + φ.apply U := by
  simp [Matrix.mulVec_add]

lemma PState.apply_smul {n : ℕ} (a : ℂ) (ψ : PState n) (U : 𝐔ₙ[n]) :
  (a • ψ).apply U = a • (ψ.apply U) := by
  simp
