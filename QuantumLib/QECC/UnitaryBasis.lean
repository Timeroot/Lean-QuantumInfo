/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import QuantumInfo.ForMathlib.HermitianMat.Unitary

/-!
# A finite family of unitaries spanning all matrices

Every matrix is a linear combination of unitaries. This file gives an explicit finite such family
on a finite-dimensional space: transpositions `swap a b`, and transpositions preceded by the sign
flip `phaseFlip a = 1 - 2 • single a a 1`. Their difference recovers the matrix unit
`single a b 1`, so the family spans.

This is the algebraic content of the *discretisation of errors*: a physical error acting on a set
of qudits, however continuous, is a linear combination of unitary errors acting on that same set.

## Main results

* `unitaryBasis` — the family, valued in the unitary group;
* `exists_unitaryBasis_expansion` — every matrix is a linear combination of it.
-/

open scoped Matrix

namespace QuantumLib

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The diagonal unitary that flips the sign of the `a`-th basis vector. -/
noncomputable def phaseFlip (a : d) : Matrix d d ℂ := 1 - (2 : ℂ) • Matrix.single a a 1

theorem single_mul_apply_same (a : d) (P : Matrix d d ℂ) (x y : d) :
    (Matrix.single a a (1 : ℂ) * P) x y = if x = a then P a y else 0 := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, eq_comm]

theorem single_mul_single_self (a : d) :
    Matrix.single a a (1 : ℂ) * Matrix.single a a 1 = Matrix.single a a 1 := by
  ext x y
  rw [single_mul_apply_same]
  simp [Matrix.single_apply, ite_and, eq_comm]

omit [Fintype d] in
theorem phaseFlip_conjTranspose (a : d) : (phaseFlip a)ᴴ = phaseFlip a := by
  rw [phaseFlip]
  ext x y
  simp [Matrix.single_apply, Matrix.one_apply, apply_ite (starRingEnd ℂ), map_ofNat, and_comm,
    eq_comm]

theorem phaseFlip_mul_self (a : d) : phaseFlip a * phaseFlip a = 1 := by
  simp only [phaseFlip, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    single_mul_single_self]
  module

theorem phaseFlip_mem_unitaryGroup (a : d) : phaseFlip a ∈ 𝐔[d] :=
  Matrix.mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, phaseFlip_conjTranspose, phaseFlip_mul_self]

theorem permMatrix_mem_unitaryGroup (σ : Equiv.Perm d) : σ.permMatrix ℂ ∈ 𝐔[d] :=
  Matrix.mem_unitaryGroup_iff.mpr <| by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one]

/-- The sign flip at `a`, as a unitary. -/
noncomputable def phaseFlipU (a : d) : 𝐔[d] := ⟨phaseFlip a, phaseFlip_mem_unitaryGroup a⟩

/-- A permutation matrix, as a unitary. -/
noncomputable def permU (σ : Equiv.Perm d) : 𝐔[d] := ⟨σ.permMatrix ℂ, permMatrix_mem_unitaryGroup σ⟩

/-- The index type of the spanning family `unitaryBasis`. -/
abbrev UnitaryBasisIndex (d : Type*) := Unit ⊕ (d × d) ⊕ (d × d)

/-- A finite family of unitaries spanning the whole matrix algebra. -/
noncomputable def unitaryBasis : UnitaryBasisIndex d → 𝐔[d]
  | .inl _ => 1
  | .inr (.inl (a, b)) => permU (Equiv.swap a b)
  | .inr (.inr (a, b)) => phaseFlipU a * permU (Equiv.swap a b)

@[simp]
theorem unitaryBasis_inl (x : Unit) : (unitaryBasis (d := d) (.inl x) : Matrix d d ℂ) = 1 := rfl

theorem single_mul_permMatrix_swap (a b : d) :
    Matrix.single a a (1 : ℂ) * (Equiv.swap a b).permMatrix ℂ = Matrix.single a b 1 := by
  ext x y
  rw [single_mul_apply_same]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Matrix.single_apply, ite_and, eq_comm]

/-- Each matrix unit is a combination of two unitaries from the family. -/
theorem single_eq_sub_smul (a b : d) :
    Matrix.single a b (1 : ℂ)
      = (2 : ℂ)⁻¹ • ((permU (Equiv.swap a b) : Matrix d d ℂ)
          - (phaseFlipU a * permU (Equiv.swap a b) : 𝐔[d])) := by
  have hperm : ((permU (Equiv.swap a b) : 𝐔[d]) : Matrix d d ℂ)
      = (Equiv.swap a b).permMatrix ℂ := rfl
  have hmul : ((phaseFlipU a * permU (Equiv.swap a b) : 𝐔[d]) : Matrix d d ℂ)
      = phaseFlip a * (Equiv.swap a b).permMatrix ℂ := rfl
  rw [hperm, hmul, phaseFlip, sub_mul, one_mul, sub_sub_cancel, smul_mul_assoc, smul_smul,
    single_mul_permMatrix_swap]
  norm_num

/-- **Every matrix is a linear combination of unitaries**, with coefficients in the explicit finite
family `unitaryBasis`. -/
theorem exists_unitaryBasis_expansion (M : Matrix d d ℂ) :
    ∃ c : UnitaryBasisIndex d → ℂ, M = ∑ k, c k • (unitaryBasis k : Matrix d d ℂ) := by
  refine ⟨Sum.elim (fun _ => 0) (Sum.elim (fun p => M p.1 p.2 / 2) fun p => -(M p.1 p.2 / 2)), ?_⟩
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_smul, Finset.sum_const_zero, zero_add]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ p : d × d,
      (M p.1 p.2 / 2) • (unitaryBasis (d := d) (.inr (.inl p)) : Matrix d d ℂ)
        + (-(M p.1 p.2 / 2)) • (unitaryBasis (d := d) (.inr (.inr p)) : Matrix d d ℂ)
        = Matrix.single p.1 p.2 (M p.1 p.2) := by
    intro p
    have hsingle : Matrix.single p.1 p.2 (M p.1 p.2)
        = M p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) := by
      ext x y
      simp [Matrix.single_apply]
    show (M p.1 p.2 / 2) • (permU (Equiv.swap p.1 p.2) : Matrix d d ℂ)
      + (-(M p.1 p.2 / 2)) • ((phaseFlipU p.1 * permU (Equiv.swap p.1 p.2) : 𝐔[d]) :
        Matrix d d ℂ) = _
    rw [hsingle, single_eq_sub_smul]
    module
  rw [Finset.sum_congr rfl fun p _ => hterm p, Fintype.sum_prod_type]
  exact Matrix.matrix_eq_sum_single M

end QuantumLib
