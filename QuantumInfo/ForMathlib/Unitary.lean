/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
    eigenspace T μ ≃ₗ[𝕜] eigenspace (U.val * T * star (U.val)) μ where
  toFun v := ⟨U.val v.val, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simp [hv]⟩
  invFun v := ⟨(star U.val) v, by
    have hv := v.2
    rw [mem_eigenspace_iff] at hv ⊢
    simpa using congrArg ((star U.val) ·) hv⟩
  map_add' := by simp
  map_smul' := by simp
  left_inv _ := by simp
  right_inv _ := by simp

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

variable {n : ℕ} (hn : Module.finrank 𝕜 E = n)

end IsSymmetric
end LinearMap
