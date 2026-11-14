/-import QuantumInfo
import LeanQEC.KroneckerLemmas

open Matrix

variable {A B R : Type*}

variable [Semiring R] [Fintype A] [DecidableEq A]

variable {dI₁ dI₂ dO₁ dO₂ : Type*} [Fintype dI₁] [Fintype dI₂]

variable [DecidableEq dI₁] [DecidableEq dI₂]


lemma MatrixMap_tensor_ext {MM₁ MM₂ : MatrixMap (dI₁ × dI₂) (dO₁ × dO₂) R}
(h_tx : ∀ (A : Matrix dI₁ dI₁ R) (B : Matrix dI₂ dI₂ R), MM₁ (Matrix.kronecker A B) = MM₂ (Matrix.kronecker A B)) : MM₁ = MM₂ := by
  apply LinearMap.ext
  intros X
  rewrite [Matrix.matrix_eq_sum_single X]
  simp [map_sum]
  congr
  ext1 A
  congr
  ext1 B
  rcases A with ⟨A1, A2⟩
  rcases B with ⟨B1, B2⟩
  rewrite [←mul_one (X (A1, A2) (B1, B2)), ←Matrix.single_kronecker_single]
  apply h_tx


variable [SMulCommClass R R R] [CommSemiring R] [Star R]

def star_conj (M : Matrix B A R) (X : Matrix A A R) :=  M * X * M.conjTranspose


def star_conj_map (M : Matrix B A R): MatrixMap A B R := {
    toFun X := M * X * M.conjTranspose
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  }


variable {M₁ : Matrix dO₁ dI₁ ℂ} {M₂ : Matrix dO₂ dI₂ ℂ}

variable [Fintype dO₁] [Fintype dO₂]

lemma conj_tensor_tensor_conj : MatrixMap.kron (star_conj_map M₁) (star_conj_map M₂) =
 star_conj_map (Matrix.kronecker M₁ M₂) := by
  apply MatrixMap_tensor_ext
  intros A B
  simp [MatrixMap.kron_map_of_kron_state, star_conj_map, kroneckerMap_conjTranspose,
  Matrix.mul_kronecker_mul]

lemma sum_conj_tensor_sum_conj_eq_sum_tensor_conj {κ₁ κ₂ : Type*} [Fintype κ₁]
 [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (M₁ N₁ : κ₁ → Matrix dO₁ dI₁ ℂ)
(M₂ N₂: κ₂ → Matrix dO₂ dI₂ ℂ) :
MatrixMap.kron (MatrixMap.of_kraus M₁ N₁) (MatrixMap.of_kraus M₂ N₂) =
MatrixMap.of_kraus (fun (i : κ₁ × κ₂) => Matrix.kronecker (M₁ i.1) (M₂ i.2)) (fun (i : κ₁ × κ₂) => Matrix.kronecker (N₁ i.1) (N₂ i.2)) := by
  apply MatrixMap_tensor_ext
  intros A B
  simp only [MatrixMap.of_kraus, Matrix.kronecker, MatrixMap.kron_map_of_kron_state,
    LinearMap.coeFn_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    kroneckerMap_conjTranspose, ← Matrix.mul_kronecker_mul]
  simp_rw [Matrix.sum_kronecker_left, Matrix.sum_kronecker_right, ←Finset.sum_product']
  simp
-/
