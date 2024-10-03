import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

open BigOperators
open Classical

namespace LinearMap
section unitary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

open Module.End

@[simp]
theorem unitary_star_apply_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    (star U.val) (U.val v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).left, one_apply]

@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (unitary.mem_iff.mp U.prop).right, one_apply]

/-- Conjugating a linear map by a unitary operator gives a map whose μ-eigenspace is
  isomorphic (same dimension) as those of the original linear map. -/
noncomputable def conj_unitary_eigenspace_equiv (T : E →ₗ[𝕜] E) (U : unitary (E →ₗ[𝕜] E)) (μ : 𝕜) :
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ := by
  constructor
  case toLinearMap =>
    constructor
    case toAddHom =>
      constructor
      case toFun =>
        rintro ⟨v,hv⟩
        use U.val v
        rw [mem_eigenspace_iff] at hv ⊢
        simp [mul_apply, hv]
      case map_add' =>
        intro x y
        simp
    intro m x
    simp
  case invFun =>
    rintro ⟨v,hv⟩
    use (star U.val) v
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv
  case left_inv =>
    intro v
    simp
  case right_inv =>
    intro v
    simp


end unitary
namespace IsSymmetric

open Module.End

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- A symmetric operator conjugated by a unitary is symmetric. -/
theorem conj_unitary_IsSymmetric (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    (U.val * T * star U.val).IsSymmetric := by
  intro i j
  rw [mul_assoc, mul_apply, ← LinearMap.adjoint_inner_right]
  rw [mul_apply, mul_apply, mul_apply, ← LinearMap.adjoint_inner_left U.val]
  exact hT (star U.val <| i) (star U.val j)

variable {n : ℕ} (hn : FiniteDimensional.finrank 𝕜 E = n)

/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. -/
def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    { σ : Equiv.Perm (Fin n) // (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  sorry --use conj_unitary_eigenspace_equiv

end IsSymmetric
end LinearMap
