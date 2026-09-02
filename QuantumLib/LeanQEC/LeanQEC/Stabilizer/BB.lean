import LeanQEC.Stabilizer.CSS
import LeanQEC.LinearAlgebra.RowspaceKernel

def Matrix.kronecker_fin {R : Type*} [Mul R] {m n p q : ℕ}
  (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin p) (Fin q) R) :
  Matrix (Fin (m * p)) (Fin (n * q)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (A.kronecker B)

@[simp]
def cyclic_shift (n k : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if ((i + k) % n) = j then 1 else 0

@[simp]
def x (l m k : ℕ) [NeZero l] : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  Matrix.kronecker_fin (cyclic_shift l k) 1

@[simp]
def y (l m k : ℕ) [NeZero m] : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  Matrix.kronecker_fin 1 (cyclic_shift m k)

variable (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)

@[simp]
def BB3_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ : Bool × ℕ)
 : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (x l m M₁.2) else (y l m M₁.2)
  let N₂ := if M₂.1 then (x l m M₂.2) else (y l m M₂.2)
  let N₃ := if M₃.1 then (x l m M₃.2) else (y l m M₃.2)
  N₁ + N₂ + N₃

@[simp]
def BB4_matrix (l m : ℕ) [NeZero l] [NeZero m] (M₁ M₂ M₃ M₄ : Bool × ℕ)
 : Matrix (Fin (l * m)) (Fin (l * m)) (ZMod 2) :=
  let N₁ := if M₁.1 then (x l m M₁.2) else (y l m M₁.2)
  let N₂ := if M₂.1 then (x l m M₂.2) else (y l m M₂.2)
  let N₃ := if M₃.1 then (x l m M₃.2) else (y l m M₃.2)
  let N₄ := if M₄.1 then (x l m M₄.2) else (y l m M₄.2)
  N₁ + N₂ + N₃ + N₄


variable {l m : ℕ} [NeZero l] [NeZero m] {M₁ M₂ M₃ : Bool × ℕ}



def Matrix.hstack_fin {α γ : Type*} {c₁ c₂ : ℕ}
(M₁ : Matrix α (Fin c₁) γ) (M₂ : Matrix α (Fin c₂) γ)
 : Matrix α (Fin (c₁ + c₂)) γ :=
 fun i j =>
  j.addCases (M₁ i) (M₂ i)

variable {l m : ℕ} [NeZero l] [NeZero m] (A₁ A₂ A₃ B₁ B₂ B₃ : Bool × ℕ)


--def BB_HX := (BB3_matrix l m A₁ A₂ A₃).hstack_fin (BB3_matrix l m B₁ B₂ B₃)
