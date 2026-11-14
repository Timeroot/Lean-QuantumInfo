import LeanQEC.Tensors
-- Define multi-qubit pauli channels to model errors

-- First define single-qubit bit-flip channel
open Qubit

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂] [Fintype dO₁] [Fintype dO₂]
variable [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

variable (U : 𝐔[Qubit])

noncomputable section


def kraus_unitary (p : ℝ) (i : Qubit): Matrix Qubit Qubit ℂ :=
  match i with
  | 0 => √(1-p) • 1
  | 1 => √p • U

@[simp] lemma kraus_unitary_0 : kraus_unitary U p 0 = √(1 - p) • 1 := by rfl

@[simp] lemma kraus_unitary_1 : kraus_unitary U p 1 = √p • U := by rfl

def kraus_bit_flip := kraus_unitary X

@[simp] lemma kraus_bit_flip_0 : kraus_bit_flip p 0 = √(1 - p) • 1 := by
  rfl

@[simp] lemma kraus_bit_flip_1 : kraus_bit_flip p 1 = √p • X := by
  rfl

def kraus_dephasing := kraus_unitary Z

@[simp] lemma kraus_dephasing_0 : kraus_dephasing p 0 = √(1 - p) • 1 := by
  rfl

@[simp] lemma kraus_dephasing_1 : kraus_dephasing p 1 = √p • Z := by
  rfl

lemma unitary_ct : (U: Matrix Qubit Qubit ℂ).conjTranspose * (U: Matrix Qubit Qubit ℂ) = 1 := by
  rw [←Matrix.star_eq_conjTranspose]
  simp only [SetLike.coe_mem, unitary.star_mul_self_of_mem]

def unitary_p_channel (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) := CPTPMap.of_kraus_CPTPMap (kraus_unitary U p) (
  by
    simp [unitary_ct, smul_smul, ←add_smul, Real.mul_self_sqrt hp1, Real.mul_self_sqrt hp2]
)

def bit_flip_channel (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1 - p) := unitary_p_channel Z p hp1 hp2

def kraus_pauli (p1 p2 p3 p4 : ℝ) (i : Fin 4): Matrix Qubit Qubit ℂ :=
  match i with
  | 0 => √p1 • 1
  | 1 => √p2 • X
  | 2 => √p3 • Y
  | 3 => √p4 • Z

def pauli_channel (p1 p2 p3 p4 : ℝ) (hp1: 0 ≤ p1) (hp2: 0 ≤ p2) (hp3: 0 ≤ p3) (hp4: 0 ≤ p4)
(hp : p1 + p2 + p3 + p4 = 1)
 := CPTPMap.of_kraus_CPTPMap (kraus_pauli p1 p2 p3 p4)
 ( by
  simp [Fin.sum_univ_four, kraus_pauli, unitary_ct, smul_smul, Real.mul_self_sqrt hp1,
    Real.mul_self_sqrt hp2, Real.mul_self_sqrt hp3, Real.mul_self_sqrt hp4, ←add_smul, hp]
 )





def kraus_depolarizing (p : ℝ) (i : Fin 4): Matrix Qubit Qubit ℂ := kraus_pauli (1-p) (p/3) (p/3) (p/3) i

def depolarizing_channel (p : ℝ) (hp1: 0 ≤ p) (hp2 : 0 ≤ 1-p) :=
pauli_channel (1-p) (p/3) (p/3) (p/3) hp2 (by linarith) (by linarith) (by linarith)

--reason about the kraus operators of channel products

variable {k : Type*} [Fintype k] [DecidableEq k]

variable {m m' n n' : Type*} (A : Matrix m m' ℂ) (B : Matrix n n' ℂ)


def kraus_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ)
(M₂ : κ₂ → Matrix dO₂ dI₂ ℂ) (hM₁ : ∑ k, (M₁ k).conjTranspose * M₁ k = 1) (hM₂ : ∑ k, (M₂ k).conjTranspose * M₂ k = 1) :
CPTPMap (dI₁ × dI₂) (dO₁ × dO₂) ℂ := CPTPMap.of_kraus_CPTPMap (fun (i : κ₁ × κ₂) => Matrix.kronecker (M₁ i.1) (M₂ i.2)) ( by
  simp [-Matrix.kronecker, kronecker_conjTranspose]
  simp [←Matrix.mul_kronecker_mul, Fintype.sum_prod_type, ←Matrix.sum_kronecker_right, ←Matrix.sum_kronecker_left, hM₁, hM₂]
)

def CPTPMap.toLinearMap_ext {dIn dOut 𝕜} [Fintype dIn] [Fintype dOut] [RCLike 𝕜] [DecidableEq dIn] {Λ₁ Λ₂ : CPTPMap dIn dOut 𝕜} (h : Λ₁.toLinearMap = Λ₂.toLinearMap) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h

def prod_kraus_is_kraus_prod {κ₁ κ₂ : Type*} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ)
(M₂ : κ₂ → Matrix dO₂ dI₂ ℂ) (hM₁ : ∑ k, (M₁ k).conjTranspose * M₁ k = 1) (hM₂ : ∑ k, (M₂ k).conjTranspose * M₂ k = 1) :
(CPTPMap.of_kraus_CPTPMap M₁ hM₁) ⊗ₖ (CPTPMap.of_kraus_CPTPMap M₂ hM₂) = kraus_prod M₁ M₂ hM₁ hM₂ := by
  apply CPTPMap.toLinearMap_ext
  apply MatrixMap_tensor_ext
  intros A B
  simp [CPTPMap.prod, sum_conj_tensor_sum_conj_eq_sum_tensor_conj M₁ M₁ M₂ M₂,
  kraus_prod, CPTPMap.of_kraus_CPTPMap]

--def two_qubit_bit_flip (p : ℝ) (hp1 : 0 ≤ p) (hp2 : 0 ≤ 1-p) := (bit_flip_channel p hp1 hp2) ⊗ₖ (bit_flip_channel p hp1 hp2)


/-
Unused sketch.  The maintained distance examples do not import the channel
development, and the intended API for arbitrary probability-unitary Kraus
families is not settled yet.
def of_kraus_prob_unitary {n : ℕ} (pfun : Fin n → ℝ) (hpfun1 : ∀ i, 0 ≤ pfun i) (hpfun2 : ∀ i, 0 ≤ 1 - pfun i)
: CPTPMap Qubit Qubit ℂ := by
  ...
-/
