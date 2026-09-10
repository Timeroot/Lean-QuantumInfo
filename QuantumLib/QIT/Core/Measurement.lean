/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Util.Matrix
public import QuantumInfo.Measurements.POVM

/-!
# Finite POVMs

A positive operator-valued measure (POVM) on a finite-dimensional system is a
finite family of positive semidefinite effects summing to the identity,
following the discrete-outcome POVM definitions and measurement-map route in
[Tomamichel2015FiniteResources, prelim.tex:303-311,813-817].

`POVM` stores its effects as `HermitianMat`s ordered against zero.  `POVM.effects`
reads the same data as bare matrices, which is the form the Born-rule traces and
the Naimark dilations work with, and `POVM.ofMatrices` builds a POVM from them.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace POVM

open QIT

universe u v w

noncomputable section

variable {x : Type u} {a : Type v}
variable [Fintype x] [Fintype a] [DecidableEq a]

/-- The effect of a POVM for outcome `y`, as a bare matrix. -/
def effects (M : POVM x a) (y : x) : CMatrix a :=
  (M.mats y).mat

/-- Each POVM effect is positive semidefinite. -/
theorem pos (M : POVM x a) (y : x) : (M.effects y).PosSemidef :=
  HermitianMat.zero_le_iff.mp (M.nonneg y)

/-- The POVM effects sum to the identity matrix. -/
@[simp]
theorem sum_eq_one (M : POVM x a) : ∑ y, M.effects y = 1 := by
  show (∑ y, (M.mats y).mat) = (1 : CMatrix a)
  rw [← HermitianMat.mat_finset_sum, M.normalized, HermitianMat.mat_one]

/-- The Born-rule probability of an outcome is the trace of the state against the effect. -/
theorem coe_measure (M : POVM x a) (rho : MState a) (y : x) :
    ((M.measure rho y : ℝ) : ℂ) = (rho.m * M.effects y).trace := by
  have h := HermitianMat.inner_eq_trace_rc (M.mats y) rho.M
  rw [DensityOp.mat_M, Matrix.trace_mul_comm] at h
  exact h

/-- A positive semidefinite matrix, read as a `HermitianMat`. -/
@[reducible]
def hermitianOfPos {A : CMatrix a} (hA : A.PosSemidef) : HermitianMat a ℂ :=
  ⟨A, selfAdjoint.mem_iff.mpr hA.isHermitian.star_eq⟩

omit [Fintype a] [DecidableEq a] in
@[simp]
theorem mat_hermitianOfPos {A : CMatrix a} (hA : A.PosSemidef) :
    (hermitianOfPos hA).mat = A :=
  rfl

/-- The POVM with the given positive semidefinite effects. -/
@[reducible]
def ofMatrices (E : x → CMatrix a) (hpos : ∀ y, (E y).PosSemidef) (hsum : ∑ y, E y = 1) :
    POVM x a where
  mats y := hermitianOfPos (hpos y)
  nonneg y := HermitianMat.zero_le_iff.mpr (hpos y)
  normalized := HermitianMat.ext <| by
    rw [HermitianMat.mat_finset_sum, HermitianMat.mat_one]
    exact hsum

@[simp]
theorem effects_ofMatrices (E : x → CMatrix a) (hpos : ∀ y, (E y).PosSemidef)
    (hsum : ∑ y, E y = 1) (y : x) :
    (ofMatrices E hpos hsum).effects y = E y :=
  rfl

/-- Two POVMs with the same effects are equal. -/
@[ext]
theorem ext_effects {M N : POVM x a} (h : M.effects = N.effects) : M = N := by
  cases M
  cases N
  congr 1
  funext y
  exact HermitianMat.ext (congrFun h y)

/-- The standard coordinate POVM in the reference basis. Its `y`th effect is
the rank-one projector `|y⟩⟨y|`. -/
def coordinate (a : Type v) [Fintype a] [DecidableEq a] : POVM a a :=
  ofMatrices (fun y => Matrix.single y y (1 : ℂ)) posSemidef_single <| by
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

/-- The binary POVM associated to a single effect `0 ≤ E ≤ 1`.

The `true` outcome is the effect `E`, while `false` is its complement. -/
def binaryOfEffect (E : CMatrix a) (hEpos : E.PosSemidef) (hEle : E ≤ 1) :
    POVM Bool a :=
  ofMatrices (fun accept => if accept then E else 1 - E)
    (fun accept => by
      by_cases h : accept
      · simp [h, hEpos]
      · have hcomp : (1 - E).PosSemidef := by
          simpa [Matrix.le_iff] using hEle
        simp [h, hcomp])
    (by
      rw [Fintype.sum_bool]
      simp)

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
    (hV : Matrix.conjTranspose V * V = 1) : POVM x a :=
  ofMatrices (fun y => Matrix.conjTranspose V * M.effects y * V)
    (fun y => by
      have hpos := (M.pos y).mul_mul_conjTranspose_same (Matrix.conjTranspose V)
      simpa [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using hpos)
    (by
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
              rw [M.sum_eq_one, Matrix.mul_one, hV])

@[simp]
theorem compressByIsometry_effects (M : POVM x b) (V : Matrix b a ℂ)
    (hV : Matrix.conjTranspose V * V = 1) (y : x) :
    (M.compressByIsometry V hV).effects y =
      Matrix.conjTranspose V * M.effects y * V :=
  rfl

end

end POVM
