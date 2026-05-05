/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import QuantumInfo.ForMathlib.HermitianMat.Unitary

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
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).left, one_apply]

@[simp]
theorem unitary_apply_star_eq (U : unitary (E →ₗ[𝕜] E)) (v : E) :
    U.val ((star U.val) v) = v := by
  rw [← mul_apply, (Unitary.mem_iff.mp U.prop).right, one_apply]

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

/-- There is an equivalence between the eigenvalues of a finite dimensional symmetric operator,
and the eigenvalues of that operator conjugated by a unitary. -/
def conj_unitary_eigenvalue_equiv (U : unitary (E →ₗ[𝕜] E)) (hT : T.IsSymmetric) :
    { σ : Equiv.Perm (Fin n) // (hT.conj_unitary_IsSymmetric U).eigenvalues hn = hT.eigenvalues hn ∘ σ } := by
  set hS := hT.conj_unitary_IsSymmetric U
  have heigen : ∀ μ, HasEigenvalue (U.val * T * star U.val) μ ↔ HasEigenvalue T μ := by
    intro μ; rw [hasEigenvalue_iff, hasEigenvalue_iff, ne_eq, ne_eq, not_iff_not,
      ← Submodule.finrank_eq_zero (R := 𝕜), ← Submodule.finrank_eq_zero (R := 𝕜),
      (conj_unitary_eigenspace_equiv T U μ).finrank_eq]
  suffices heq : hS.eigenvalues hn = hT.eigenvalues hn by exact ⟨1, by simp [heq]⟩
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedGE
    (hS.eigenvalues_antitone hn).sortedGE_ofFn (hT.eigenvalues_antitone hn).sortedGE_ofFn
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]; ext a
  simp only [Multiset.count_map]
  suffices ∀ (R : E →ₗ[𝕜] E) (hR : R.IsSymmetric),
      (Multiset.filter (fun x => a = hR.eigenvalues hn x) Finset.univ.val).card =
      Finset.card {i | (hR.eigenvalues hn i : 𝕜) = ↑a} from by
    rw [this _ hS, this _ hT]
    by_cases ha : HasEigenvalue T (↑a : 𝕜)
    · rw [hS.card_filter_eigenvalues_eq hn (heigen _|>.mpr ha),
          hT.card_filter_eigenvalues_eq hn ha,
          (conj_unitary_eigenspace_equiv T U ↑a).finrank_eq]
    · have h1 : ∀ i, hT.eigenvalues hn i ≠ a :=
        fun i h => ha (h ▸ hT.hasEigenvalue_eigenvalues hn i)
      have h2 : ∀ i, hS.eigenvalues hn i ≠ a :=
        fun i h => mt (heigen _).mp ha (h ▸ hS.hasEigenvalue_eigenvalues hn i)
      simp [h1, h2]
  intro R hR
  change Finset.card (Finset.univ.filter (fun x => a = hR.eigenvalues hn x)) = _
  congr 1; ext i; simp [eq_comm]

end IsSymmetric
end LinearMap
