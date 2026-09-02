import Mathlib

lemma is_herm_of_kron_herm
  {A B : Type*} [Fintype A] [Fintype B]
  [CommMagma R] [StarMul R]
  {M₁ : Matrix A A R} {M₂ : Matrix B B R}
  (hM₁ : M₁.IsHermitian) (hM₂ : M₂.IsHermitian) :
  (Matrix.kronecker M₁ M₂).IsHermitian := by
  simp [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hM₁.eq, hM₂.eq]


variable {dI₁ dI₂ dO₁ dO₂ : Type*} [DecidableEq dI₁] [DecidableEq dI₂] [DecidableEq dO₁] [DecidableEq dO₂]

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]

variable {R : Type*}  [Semiring R] [SMulCommClass R R R] [Star R] [StarMul R]

variable {m m' n n' : Type*} (A : Matrix m m' ℂ) (B : Matrix n n' ℂ)

theorem kronecker_conjTranspose : (A.kronecker B).conjTranspose = (Matrix.kronecker A.conjTranspose B.conjTranspose) := by
  ext; simp

theorem kroneckerMap_conjTranspose : (Matrix.kroneckerMap (fun (x1 x2) => x1 * x2) A B).conjTranspose = (Matrix.kroneckerMap (fun (x1 x2) => x1 * x2) A.conjTranspose B.conjTranspose) := by
  ext; simp


theorem Matrix.finset_sum_kronecker {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α]  (K : Finset (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k ∈ K, k) B = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) k B  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_left, IH]
    intros c d e
    rw [right_distrib]

theorem Matrix.sum_kronecker_label_finset_left {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] (K : Finset κ) (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k ∈ K, (M k)) B = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) (M k) B  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_left, IH]
    intros c d e
    rw [right_distrib]

theorem Matrix.sum_kronecker_label_finset_right {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] (K : Finset κ) (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (∑ k ∈ K, (M k)) = ∑ k ∈ K, kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (M k)  := by
  refine (Finset.induction_on K ?_ ?_)
  · simp
  · intro A M hAM IH
    rw [Finset.sum_insert hAM, Finset.sum_insert hAM, Matrix.kroneckerMap_add_right, IH]
    intros c d e
    rw [left_distrib]


theorem Matrix.sum_kronecker_left {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] [Fintype κ] (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) (∑ k, M k) B = ∑ k, kroneckerMap (fun (x1 x2 : α) => x1 * x2) (M k) B  := Matrix.sum_kronecker_label_finset_left (Finset.univ) M B

theorem Matrix.sum_kronecker_right {α : Type u_2} {l : Type u_8} {m : Type u_9}
{n : Type u_10} {p : Type u_11} [Semiring α] [Fintype l] [Fintype m] [DecidableEq α] {κ : Type*} [DecidableEq κ] [Fintype κ] (M : κ → (Matrix l m α)) (B : Matrix n p α) :
kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (∑ k, M k) = ∑ k, kroneckerMap (fun (x1 x2 : α) => x1 * x2) B (M k)  := Matrix.sum_kronecker_label_finset_right (Finset.univ) M B



/- can't get dimensions to work, keep thinking about this
lemma sum_conj_tensor_sum_conj_eq_sum_tensor_conj {κ₁ κ₂ : Type*} [Fintype κ₁]
 [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (M₁ : κ₁ → Matrix dO₁ dI₁ ℂ)
(M₂ : κ₂ → Matrix dO₂ dI₂ ℂ) :
  Matrix.kronecker (fun (X : Matrix dI₁ dI₁ ℂ) => ∑ k : κ₁, star_conj (M₁ k) X) (fun (X : Matrix dI₂ dI₂ ℂ) => ∑ k : κ₂, star_conj (M₂ k) X) =
  fun (X : Matrix (dI₁ × dI₂) (dI₁ × dI₂) ℂ) => (∑ (k : κ₁ × κ₂), star_conj (Matrix.kronecker (M₁ k.1) (M₂ k.2)) X)
 := by admit
-/
