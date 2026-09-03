/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Normed

/-!
# Positive-semidefinite cone as a proper cone

The cone of PSD `CMatrix n` matrices as a `ProperCone ℝ (CMatrix n)`.
Foundation for conic/SDP strong duality.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

open Matrix Continuous Complex

namespace QIT

universe u

variable (n : Type u)

/-- A real nonneg scalar preserves PSD. -/
private theorem posSemidef_real_smul (c : ℝ) (hc : 0 ≤ c) {M : CMatrix n} (hM : M.PosSemidef) :
    (c • M).PosSemidef := by
  rw [Matrix.PosSemidef]
  refine ⟨?_, ?_⟩
  · show conjTranspose (c • M) = c • M
    rw [Matrix.conjTranspose_smul, hM.1]
    simp
  · intro x
    show 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * (c • M) i j * xj
    have hpull : x.sum (fun i xi => x.sum (fun j xj =>
        star xi * (c • M) i j * xj)) =
        (c:ℂ) * x.sum (fun i xi => x.sum (fun j xj =>
        star xi * M i j * xj)) := by
      simp only [Finsupp.sum, Finsupp.sum, Matrix.smul_apply, Complex.real_smul,
        Finset.mul_sum, mul_comm, mul_assoc, mul_left_comm]
    rw [hpull]
    have hc' : 0 ≤ (c:ℂ) := by simp [Complex.le_def, hc]
    exact mul_nonneg hc' (hM.2 x)

section FintypeDecidable

variable [Fintype n] [DecidableEq n]

/-- PSD cone as an `ℝ≥0`-submodule. -/
def psdSubmodule : Submodule NNReal (CMatrix n) :=
  { carrier := { A | A.PosSemidef }
    zero_mem' := (le_refl (0 : CMatrix n)).posSemidef
    add_mem' := fun {A B} hA hB => (add_nonneg hA.nonneg hB.nonneg).posSemidef
    smul_mem' := fun c _ hA => by
      rw [NNReal.smul_def]
      exact posSemidef_real_smul n (c : ℝ) (NNReal.coe_nonneg c) hA }

end FintypeDecidable

private theorem continuous_conjTranspose' : Continuous (fun A : CMatrix n => conjTranspose A) := by
  refine continuous_pi ?_; intro i
  refine continuous_pi ?_; intro j
  exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))

private theorem isClosed_setOf_zero_le_complex : IsClosed ({z : ℂ | 0 ≤ z} : Set ℂ) := by
  have h : ({z : ℂ | 0 ≤ z} : Set ℂ) = {z | 0 ≤ z.re} ∩ {z | z.im = 0} := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; constructor
    · intro hz; simp [Complex.le_def] at hz ⊢; tauto
    · rintro ⟨hre, him⟩; simp [Complex.le_def]; exact ⟨hre, him.symm⟩
  rw [h]
  exact (isClosed_Ici.preimage continuous_re).inter
    (isClosed_singleton.preimage continuous_im)

private theorem entry_continuous (i j : n) : Continuous (fun A : CMatrix n => A i j) :=
  (continuous_apply j).comp (continuous_apply i)

/-- Quadratic form `xᴴAx` is continuous in `A`. -/
private theorem continuous_quadraticForm (x : n →₀ ℂ) :
    Continuous (fun A : CMatrix n =>
      (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj)) := by
  classical
  simp only [Finsupp.sum, Finsupp.sum]
  exact continuous_finsetSum x.support fun i _ =>
    continuous_finsetSum x.support fun j _ =>
      Continuous.mul (Continuous.mul continuous_const (entry_continuous n i j)) continuous_const

section FintypeDecidable

variable [Fintype n] [DecidableEq n]

/-- PSD cone as a `ProperCone ℝ (CMatrix n)`. -/
def psdCone : ProperCone ℝ (CMatrix n) :=
  { psdSubmodule n with
    isClosed' := by
      show IsClosed ({A | A.PosSemidef} : Set (CMatrix n))
      have h : ({A | A.PosSemidef} : Set (CMatrix n)) =
          ({A | A.IsHermitian} ∩
            (⋂ x : n →₀ ℂ,
              {A : CMatrix n | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj})) := by
        ext A; simp [Matrix.PosSemidef, Set.mem_iInter]
      rw [h]
      refine IsClosed.inter ?herm ?quad
      · have hH : {A : CMatrix n | A.IsHermitian} = {A | conjTranspose A = A} := by
          ext A; simp [Matrix.IsHermitian]
        rw [hH]; exact isClosed_eq (continuous_conjTranspose' n) continuous_id
      · exact isClosed_iInter fun x =>
          isClosed_setOf_zero_le_complex.preimage (continuous_quadraticForm n x) }

omit [Fintype n] [DecidableEq n] in
theorem psdCone_mem (A : CMatrix n) : A ∈ psdCone n ↔ A.PosSemidef := Iff.rfl

end FintypeDecidable

end QIT
