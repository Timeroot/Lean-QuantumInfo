/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix

/-!
# Finite POVMs

A positive operator-valued measure (POVM) on a finite-dimensional system is a
finite family of positive semidefinite effects summing to the identity,
following the discrete-outcome POVM definitions and measurement-map route in
[Tomamichel2015FiniteResources, prelim.tex:303-311,813-817].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w

noncomputable section

variable {x : Type u} {a : Type v}
variable [Fintype x] [Fintype a] [DecidableEq a]

/-- A finite discrete POVM with outcomes indexed by `x`. -/
structure POVM (x : Type u) (a : Type v) [Fintype x] [Fintype a] [DecidableEq a] where
  /-- The POVM effect for outcome `x`. -/
  effects : x → CMatrix a
  /-- Each effect is positive semidefinite. -/
  pos : ∀ y, (effects y).PosSemidef
  /-- The effects sum to the identity. -/
  sum_eq_one : ∑ y, effects y = 1

namespace POVM

/-- The standard coordinate POVM in the reference basis. Its `y`th effect is
the rank-one projector `|y⟩⟨y|`. -/
def coordinate (a : Type v) [Fintype a] [DecidableEq a] : POVM a a where
  effects y := Matrix.single y y (1 : ℂ)
  pos y := posSemidef_single y
  sum_eq_one := by
    ext i j
    rw [Matrix.sum_apply]
    by_cases hij : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · rw [Matrix.single_apply]
        simp
      · intro y _ hy
        rw [Matrix.single_apply]
        simp [hy]
      · intro hi
        simp at hi
    · rw [Matrix.one_apply, if_neg hij]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [Matrix.single_apply]
      have hnot : ¬ (y = i ∧ y = j) := by
        intro h
        exact hij (h.1.symm.trans h.2)
      simp [hnot]

@[simp]
theorem coordinate_effects {a : Type v} [Fintype a] [DecidableEq a] (y : a) :
    (coordinate a).effects y = Matrix.single y y (1 : ℂ) :=
  rfl

variable (M : POVM x a)

/-- The POVM effects sum to the identity matrix. -/
@[simp]
theorem sum_effects : ∑ y, M.effects y = 1 := M.sum_eq_one

/-- The binary POVM associated to a single effect `0 <= E <= 1`.

The `true` outcome is the effect `E`, while `false` is its complement. -/
def binaryOfEffect (E : CMatrix a) (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    POVM Bool a where
  effects accept := if accept then E else 1 - E
  pos accept := by
    by_cases h : accept
    · simp [h, hEpos]
    · have hcomp : (1 - E).PosSemidef := by
        simpa [Matrix.le_iff] using hEle
      simp [h, hcomp]
  sum_eq_one := by
    rw [Fintype.sum_bool]
    simp

@[simp]
theorem binaryOfEffect_true_effect (E : CMatrix a) (hEpos : E.PosSemidef)
    (hEle : E ≤ 1) :
    (binaryOfEffect E hEpos hEle).effects true = E :=
  rfl

@[simp]
theorem binaryOfEffect_false_effect (E : CMatrix a) (hEpos : E.PosSemidef)
    (hEle : E ≤ 1) :
    (binaryOfEffect E hEpos hEle).effects false = 1 - E :=
  rfl

variable {b : Type w} [Fintype b] [DecidableEq b]

/-- Compress a POVM on a larger finite system along an isometric embedding.

If `V : b → a` satisfies `Vᴴ V = 1`, then each effect `E_y` on `b` pulls back
to `Vᴴ E_y V` on `a`.  This is the operational POVM obtained by applying the
larger-space measurement after the isometric embedding. -/
def compressByIsometry (M : POVM x b) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = 1) : POVM x a where
  effects y := Matrix.conjTranspose V * M.effects y * V
  pos y := by
    have hpos := (M.pos y).mul_mul_conjTranspose_same (Matrix.conjTranspose V)
    simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hpos
  sum_eq_one := by
    have hsum :
        (∑ y, Matrix.conjTranspose V * M.effects y * V) =
          Matrix.conjTranspose V * (∑ y, M.effects y) * V := by
      calc
        (∑ y, Matrix.conjTranspose V * M.effects y * V) =
            (∑ y, (Matrix.conjTranspose V * M.effects y) * V) := by
              rfl
        _ = (∑ y, Matrix.conjTranspose V * M.effects y) * V := by
              rw [Matrix.sum_mul]
        _ = (Matrix.conjTranspose V * (∑ y, M.effects y)) * V := by
              rw [Matrix.mul_sum]
        _ = Matrix.conjTranspose V * (∑ y, M.effects y) * V := by
              rw [Matrix.mul_assoc]
    calc
      (∑ y, Matrix.conjTranspose V * M.effects y * V) =
          Matrix.conjTranspose V * (∑ y, M.effects y) * V := hsum
      _ = 1 := by
            rw [M.sum_eq_one, Matrix.mul_one, hV]

@[simp]
theorem compressByIsometry_effects (M : POVM x b) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = 1) (y : x) :
    (M.compressByIsometry V hV).effects y =
      Matrix.conjTranspose V * M.effects y * V :=
  rfl

end POVM

end

end QIT
