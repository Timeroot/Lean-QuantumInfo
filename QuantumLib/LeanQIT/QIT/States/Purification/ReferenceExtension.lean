/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Purification.PartialIsometry
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reference-side isometry extension

This module isolates the third finite-dimensional linear-algebra step needed
by the purification-equivalence route registered from [Wilde2011Qst,
qit-notes.tex:10320-10338] and [Gour2024Resources,
BookQRT.tex:2051-2069].

The statements stay at the abstract `LinearIsometry`/`Submodule` layer: matrix
coordinates, `ReferenceIsometry`, `PureVector`, fidelity, and Uhlmann's theorem
are handled by downstream leaves.
-/

@[expose] public section

namespace QIT

noncomputable section

namespace LinearIsometry

open Module

variable {E₁ E₂ : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]

/-- A finite-dimensional complex inner-product space embeds isometrically into
any finite-dimensional complex inner-product space of at least the same
dimension. -/
private def ofFinrankLE
    (hfin : finrank ℂ E₁ ≤ finrank ℂ E₂) :
    E₁ →ₗᵢ[ℂ] E₂ := by
  classical
  let b₁ := stdOrthonormalBasis ℂ E₁
  let b₂ := stdOrthonormalBasis ℂ E₂
  let f : E₁ →ₗ[ℂ] E₂ := b₁.toBasis.constr ℂ fun i => b₂ (Fin.castLE hfin i)
  have hf : Orthonormal ℂ (f ∘ b₁.toBasis) := by
    rw [show f ∘ b₁.toBasis = fun i : Fin (finrank ℂ E₁) => b₂ (Fin.castLE hfin i) by
      funext i
      simp [f, b₁]]
    exact b₂.orthonormal.comp (Fin.castLE hfin) (Fin.castLE_injective hfin)
  exact f.isometryOfOrthonormal b₁.orthonormal hf

/-- Extend a subspace isometry into a larger finite-dimensional target space.

This is the reference-side extension step used after constructing the partial
isometry between adjoint ranges. It does not mention matrices or
purifications. -/
theorem exists_extension_of_finrank_le
    (S : Submodule ℂ E₁) (U : S →ₗᵢ[ℂ] E₂)
    (hfin : finrank ℂ E₁ ≤ finrank ℂ E₂) :
    ∃ V : E₁ →ₗᵢ[ℂ] E₂, ∀ x : S, V x = U x := by
  classical
  let LS : Submodule ℂ E₂ := LinearMap.range U.toLinearMap
  have hLS : finrank ℂ LS = finrank ℂ S :=
    LinearMap.finrank_range_of_inj U.injective
  have hperp : finrank ℂ Sᗮ ≤ finrank ℂ LSᗮ := by
    calc
      finrank ℂ Sᗮ = finrank ℂ E₁ - finrank ℂ S := by
        simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
      _ ≤ finrank ℂ E₂ - finrank ℂ S := Nat.sub_le_sub_right hfin _
      _ = finrank ℂ E₂ - finrank ℂ LS := by rw [hLS]
      _ = finrank ℂ LSᗮ := by
        simp only [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
  let E : Sᗮ →ₗᵢ[ℂ] LSᗮ := ofFinrankLE hperp
  let L3 : Sᗮ →ₗᵢ[ℂ] E₂ := LSᗮ.subtypeₗᵢ.comp E
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  haveI : CompleteSpace E₁ := FiniteDimensional.complete ℂ E₁
  let p1 := S.orthogonalProjection.toLinearMap
  let p2 := Sᗮ.orthogonalProjection.toLinearMap
  let M : E₁ →ₗ[ℂ] E₂ := U.toLinearMap.comp p1 + L3.toLinearMap.comp p2
  have M_norm_map : ∀ x : E₁, ‖M x‖ = ‖x‖ := by
    intro x
    have Mx_decomp : M x = U (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
    have Mx_orth : inner ℂ (U (p1 x)) (L3 (p2 x)) = 0 := by
      have Lp1x : U (p1 x) ∈ LS :=
        LinearMap.mem_range_self U.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) ∈ LSᗮ := by
        simp only [L3, LS, ← Submodule.range_subtype LSᗮ]
        exact LinearMap.mem_range_self LSᗮ.subtype (E (p2 x))
      exact Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      Submodule.norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (U (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map, ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  refine ⟨{ toLinearMap := M, norm_map' := M_norm_map }, ?_⟩
  intro s
  change M (s : E₁) = U s
  have hp1 : p1 (s : E₁) = s :=
    Submodule.orthogonalProjection_mem_subspace_eq_self s
  have hp2 : p2 (s : E₁) = 0 := by
    exact Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
      (K := Sᗮ) (by simp [Submodule.orthogonal_orthogonal, Submodule.coe_mem s])
  simp [M, hp1, hp2]

end LinearIsometry

namespace LinearMap

open Module

variable {E₁ E₂ F : Type*}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [FiniteDimensional ℂ E₂]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Equal target-side Gram operators give a full-domain isometry sending
`T₁.adjoint y` to `T₂.adjoint y`. -/
theorem exists_isometry_apply_adjoint_of_comp_adjoint_eq
    {T₁ : E₁ →ₗ[ℂ] F} {T₂ : E₂ →ₗ[ℂ] F}
    (hGram : T₁.comp T₁.adjoint = T₂.comp T₂.adjoint)
    (hfin : finrank ℂ E₁ ≤ finrank ℂ E₂) :
    ∃ V : E₁ →ₗᵢ[ℂ] E₂, ∀ y : F, V (T₁.adjoint y) = T₂.adjoint y := by
  classical
  let S : Submodule ℂ E₁ := LinearMap.range T₁.adjoint
  let U : S →ₗᵢ[ℂ] E₂ :=
    (LinearMap.range T₂.adjoint).subtypeₗᵢ.comp (adjointRangeIsometry hGram)
  obtain ⟨V, hV⟩ := LinearIsometry.exists_extension_of_finrank_le S U hfin
  refine ⟨V, ?_⟩
  intro y
  simpa [S, U, adjointRangeIsometry_apply_adjoint] using
    hV ⟨T₁.adjoint y, LinearMap.mem_range_self T₁.adjoint y⟩

end LinearMap

end

end QIT
