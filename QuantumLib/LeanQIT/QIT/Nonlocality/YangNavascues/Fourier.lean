/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Nonlocality.YangNavascues.BobLocal
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Data.ZMod.Basic

/-!
# Finite Fourier and controlled operators for Yang-Navascues

This module provides the finite Fourier and controlled local-operator API used
by the Coladangelo-Goh-Scarani proof of the Yang-Navascues sufficient
self-testing criterion.  It deliberately stops before the final density
calculation that consumes these operators to prove the local-isometry output.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

namespace QIT
namespace YangNavascues

universe u v w

noncomputable section

/-- The standard Fourier root on `ZMod d`, transported to the `Fin d` API. -/
def fourierRoot (d : ℕ) [NeZero d] : ℂ :=
  ZMod.stdAddChar (1 : ZMod d)

/-- The normalizing scalar for the unitary Fourier matrix. -/
def fourierScale (d : ℕ) : ℂ :=
  (((Real.sqrt (d : ℝ)) : ℂ)⁻¹)

/-- The normalized finite Fourier matrix on `Fin d`. -/
def fourierMatrix (d : ℕ) [NeZero d] : CMatrix (Fin d) :=
  fun i j =>
    fourierScale d *
      ZMod.stdAddChar (ZMod.finEquiv d i * ZMod.finEquiv d j)

/-- The inverse finite Fourier matrix. -/
def inverseFourierMatrix (d : ℕ) [NeZero d] : CMatrix (Fin d) :=
  Matrix.conjTranspose (fourierMatrix d)

/-- Orthogonality of the standard additive characters on `ZMod d`. -/
theorem zmod_character_sum (d : ℕ) [NeZero d] (t : ZMod d) :
    ∑ i : ZMod d, ZMod.stdAddChar (t * i) = if t = 0 then (d : ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar d h)

private theorem fourier_scale_norm (d : ℕ) [NeZero d] :
    star (fourierScale d) * fourierScale d * (d : ℂ) = 1 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  have hsq : (((Real.sqrt d : ℝ) : ℂ) ^ 2) = (d : ℂ) := by
    have hreal : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg d)
    exact_mod_cast hreal
  simp [fourierScale]
  calc
    ((Real.sqrt d : ℝ) : ℂ)⁻¹ * ((Real.sqrt d : ℝ) : ℂ)⁻¹ * (d : ℂ)
        = (((Real.sqrt d : ℝ) : ℂ) ^ 2)⁻¹ * (d : ℂ) := by ring
    _ = (d : ℂ)⁻¹ * (d : ℂ) := by rw [hsq]
    _ = 1 := inv_mul_cancel₀ hdne

private theorem circle_star_mul_self (z : Circle) :
    star (z : ℂ) * (z : ℂ) = 1 := by
  have h : (Complex.normSq (z : ℂ) : ℂ) = star (z : ℂ) * (z : ℂ) :=
    Complex.normSq_eq_conj_mul_self
  rw [Circle.normSq_coe] at h
  simpa [Complex.star_def] using h.symm

private theorem stdAddChar_star_mul (d : ℕ) [NeZero d] (a b : ZMod d) :
    star (ZMod.stdAddChar a) * ZMod.stdAddChar b = ZMod.stdAddChar (b - a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
  have hstar :
      star ((ZMod.toCircle a : Circle) : ℂ) = (((ZMod.toCircle a : Circle) : ℂ))⁻¹ := by
    have h := circle_star_mul_self (ZMod.toCircle a)
    exact eq_inv_of_mul_eq_one_left h
  rw [hstar, ← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  rw [← (ZMod.toCircle : AddChar (ZMod d) Circle).map_neg_eq_inv]
  rw [← (ZMod.toCircle : AddChar (ZMod d) Circle).map_add_eq_mul]
  congr 1
  abel

/-- The normalized finite Fourier matrix is unitary. -/
theorem fourierMatrix_isUnitary (d : ℕ) [NeZero d] :
    Matrix.conjTranspose (fourierMatrix d) * fourierMatrix d = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierMatrix]
  have hsum :
      (∑ x : Fin d,
          star (fourierScale d * ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d i)) *
            (fourierScale d * ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d j))) =
        star (fourierScale d) * fourierScale d *
          (∑ x : ZMod d,
            ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * x)) := by
    calc
      (∑ x : Fin d,
          star (fourierScale d * ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d i)) *
            (fourierScale d * ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d j))) =
          ∑ x : Fin d,
            star (fourierScale d) * fourierScale d *
              ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * ZMod.finEquiv d x) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            calc
              star (fourierScale d *
                    ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d i)) *
                  (fourierScale d *
                    ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d j)) =
                  star (fourierScale d) * fourierScale d *
                    (star (ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d i)) *
                      ZMod.stdAddChar (ZMod.finEquiv d x * ZMod.finEquiv d j)) := by
                    rw [star_mul]
                    ring
              _ = star (fourierScale d) * fourierScale d *
                    ZMod.stdAddChar
                      ((ZMod.finEquiv d j - ZMod.finEquiv d i) * ZMod.finEquiv d x) := by
                    rw [stdAddChar_star_mul]
                    congr 2
                    ring
      _ = star (fourierScale d) * fourierScale d *
          (∑ x : Fin d,
            ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * ZMod.finEquiv d x)) := by
            rw [Finset.mul_sum]
      _ = star (fourierScale d) * fourierScale d *
          (∑ x : ZMod d,
            ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * x)) := by
            congr 1
            exact Fintype.sum_equiv (ZMod.finEquiv d).toEquiv
              (fun x : Fin d =>
                ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * ZMod.finEquiv d x))
              (fun x : ZMod d =>
                ZMod.stdAddChar ((ZMod.finEquiv d j - ZMod.finEquiv d i) * x))
              (by intro x; rfl)
  rw [hsum]
  by_cases hij : i = j
  · subst j
    have hchar :
        (∑ x : ZMod d,
            ZMod.stdAddChar (((ZMod.finEquiv d) i - (ZMod.finEquiv d) i) * x)) =
          (d : ℂ) := by
      simp
    rw [hchar]
    simpa using fourier_scale_norm d
  · have hzij : (ZMod.finEquiv d j - ZMod.finEquiv d i : ZMod d) ≠ 0 := by
      intro hzero
      apply hij
      apply (ZMod.finEquiv d).injective
      exact (sub_eq_zero.mp hzero).symm
    rw [zmod_character_sum, if_neg hzij]
    simp [hij]

/-- The inverse Fourier matrix is a left inverse to the Fourier matrix. -/
theorem inverseFourierMatrix_mul_fourierMatrix (d : ℕ) [NeZero d] :
    inverseFourierMatrix d * fourierMatrix d = 1 := by
  simpa [inverseFourierMatrix] using fourierMatrix_isUnitary d

/-- A block-controlled operator on `H × Fin d`. -/
def controlledOperator {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → CMatrix H) : CMatrix (H × Fin d) :=
  fun x y => if x.2 = y.2 then U x.2 x.1 y.1 else 0

@[simp]
theorem controlledOperator_apply {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → CMatrix H)
    (h h' : H) (k k' : Fin d) :
    controlledOperator U (h, k) (h', k') =
      if k = k' then U k h h' else 0 :=
  rfl

/-- Controlled local-unitary operator `|k><k|`-controlled by the ancilla. -/
def controlledUnitary {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (U : Fin d → Matrix.unitaryGroup H ℂ) : CMatrix (H × Fin d) :=
  controlledOperator fun k => (U k : CMatrix H)

/-- Phase operator `sum_k omega^k P_k + (1 - sum_k P_k)`. -/
def phaseOperator {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) : CMatrix H :=
  (∑ k : Fin d, (fourierRoot d) ^ (k : ℕ) • P k) +
    (1 - ∑ k : Fin d, P k)

/-- Controlled powers of a phase operator. -/
def controlledPhase {H : Type u} [Fintype H] [DecidableEq H]
    {d : ℕ} [NeZero d] (P : Fin d → CMatrix H) : CMatrix (H × Fin d) :=
  controlledOperator fun k => phaseOperator P ^ (k : ℕ)

namespace YNData

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

variable (data : YNData ι HA HB)

/-- Alice's CGS controlled phase operator, using an explicit finite ordering. -/
def aliceControlledPhase (e : ι ≃ Fin (Fintype.card ι)) :
    CMatrix (HA × Fin (Fintype.card ι)) :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  controlledPhase fun k => data.aliceProjection.effects (e.symm k)

/-- Alice's controlled `X_A^(k)` operator, using an explicit finite ordering. -/
def aliceControlledUnitary (e : ι ≃ Fin (Fintype.card ι)) :
    CMatrix (HA × Fin (Fintype.card ι)) :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  controlledUnitary fun k => data.aliceUnitary (e.symm k)

/-- Bob's controlled `X_B^(k)` operator, using an explicit finite ordering. -/
def bobControlledUnitary (e : ι ≃ Fin (Fintype.card ι)) :
    CMatrix (HB × Fin (Fintype.card ι)) :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  controlledUnitary fun k => data.bobUnitary (e.symm k)

end YNData

namespace BobLocalOrthogonalization

variable {ι : Type u} {HA : Type v} {HB : Type w}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
variable {data : YNData ι HA HB} {rho : State (HA × HB)}

variable (W : BobLocalOrthogonalization data rho)

/-- Bob's CGS controlled phase operator built from the Bob-local replacement family. -/
def bobControlledPhase (e : ι ≃ Fin (Fintype.card ι)) :
    CMatrix (HB × Fin (Fintype.card ι)) :=
  haveI : Nonempty ι := ⟨data.target.base⟩
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  controlledPhase fun k => (W.bobLocal (e.symm k)).matrix

end BobLocalOrthogonalization

end

end YangNavascues
end QIT
