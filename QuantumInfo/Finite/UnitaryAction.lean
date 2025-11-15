/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati, Ruize Chen
-/

import QuantumInfo.Finite.new_Braket
import QuantumInfo.Finite.Unitary
import Mathlib

variable {d : Type*} [Fintype d] [DecidableEq d]
open Matrix

/-- Apply a unitary `U : 𝐔[d]` to a ket `ψ : KetEuc d`.
We view the matrix as a unitary continuous linear map on `EuclideanSpace ℂ d`,
then use `unitary.norm_map` to show normalization is preserved. -/
noncomputable def optKet (U: 𝐔[d]) (ψ : KetEuc d): KetEuc d where
  vec :=  Matrix.mulVec (U : Matrix d d ℂ) ψ.vec
  normalized' := by
    have hU: LinearMap.toContinuousLinearMap (U : Matrix d d ℂ).toEuclideanLin ∈ unitary (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) := by
      rw [unitary, Submonoid.mem_mk, Subsemigroup.mem_mk]
      have hU1 := Matrix.UnitaryGroup.star_mul_self U
      have hU2 :  (U : Matrix d d ℂ) * star (U : Matrix d d ℂ) = 1:= mul_eq_one_comm.mp hU1
      constructor
      · ext x ex
        simp only [ContinuousLinearMap.coe_mul, Function.comp_apply, ContinuousLinearMap.one_apply]
        rw [ContinuousLinearMap.star_eq_adjoint]
        erw [LinearMap.coe_toContinuousLinearMap' (U : Matrix d d ℂ).mulVecLin]
        rw [← ContinuousLinearMap.coe_coe, ← LinearMap.adjoint_eq_toCLM_adjoint,
          mulVecBilin_apply, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          Matrix.toEuclideanLin_apply, PiLp.toLp_apply, WithLp.ofLp, id_eq, mulVec_mulVec]
        erw [hU1]
        rw [one_mulVec]
      · ext x ex
        rw [ContinuousLinearMap.coe_mul, LinearMap.coe_toContinuousLinearMap',
          Function.comp_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.star_eq_adjoint]
        erw [LinearMap.coe_toContinuousLinearMap' (U : Matrix d d ℂ).mulVecLin]
        rw [← ContinuousLinearMap.coe_coe, ← LinearMap.adjoint_eq_toCLM_adjoint,
          mulVecBilin_apply, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
            Matrix.toEuclideanLin_apply, WithLp.ofLp, WithLp.toLp, id_eq, mulVec_mulVec, id_eq]
        erw [hU2]
        rw [one_mulVec]
    let Umap: unitary (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) := ⟨(U : Matrix d d ℂ).mulVecLin.toContinuousLinearMap,hU⟩
    have hUU := unitary.norm_map Umap ψ.vec
    simp only at hUU
    rw [← ψ.normalized', ← hUU]
    rfl
