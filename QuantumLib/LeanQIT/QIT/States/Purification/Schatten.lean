/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.States.Schatten
public import QIT.States.Purification.Gram

/-!
# Schatten expressions for complementary pure-state marginals

This module records the finite-dimensional Schmidt-spectrum bridge used by the
EA capacity route: the two partial traces of a rank-one bipartite pure
operator have the same nonzero eigenvalues, hence the same positive power
traces and PSD Schatten expressions.  This is the source route in
KhatriWilde2024Principles, Chapters/EA_capacity.tex lines 2197-2204.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QIT

universe u v

noncomputable section

variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

private def rankOneAmplitudeMatrix (psi : Prod r a → ℂ) : Matrix a r ℂ :=
  fun x i => psi (i, x)

omit [Fintype r] [DecidableEq r] [DecidableEq a] in
private theorem partialTraceB_rankOneMatrix_eq_transpose_rankOneAmplitudeMatrix_mul_conjTranspose
    (psi : Prod r a → ℂ) :
    partialTraceB (a := r) (b := a) (rankOneMatrix psi) =
      Matrix.transpose (rankOneAmplitudeMatrix psi) *
        Matrix.conjTranspose (Matrix.transpose (rankOneAmplitudeMatrix psi)) := by
  ext i j
  simp [partialTraceB, rankOneMatrix_apply, rankOneAmplitudeMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]

omit [DecidableEq r] [Fintype a] [DecidableEq a] in
private theorem partialTraceA_rankOneMatrix_eq_rankOneAmplitudeMatrix_mul_conjTranspose
    (psi : Prod r a → ℂ) :
    partialTraceA (a := r) (b := a) (rankOneMatrix psi) =
      rankOneAmplitudeMatrix psi * Matrix.conjTranspose (rankOneAmplitudeMatrix psi) := by
  ext x y
  simp [partialTraceA, rankOneMatrix_apply, rankOneAmplitudeMatrix, Matrix.mul_apply]

/-- The two partial traces of an arbitrary finite-dimensional rank-one
bipartite operator have equal positive power traces. -/
theorem psdTracePower_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
    (psi : Prod r a → ℂ) {p : ℝ} (hp : 0 < p) :
    psdTracePower
        (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi)) p =
      psdTracePower
        (partialTraceA (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceA_posSemidef (rankOneMatrix_pos psi)) p := by
  let A : Matrix a r ℂ := rankOneAmplitudeMatrix psi
  let AT : Matrix r a ℂ := Matrix.transpose A
  have hLeft :
      partialTraceB (a := r) (b := a) (rankOneMatrix psi) =
        AT * Matrix.conjTranspose AT := by
    simpa [A, AT] using
      partialTraceB_rankOneMatrix_eq_transpose_rankOneAmplitudeMatrix_mul_conjTranspose psi
  have hRight :
      partialTraceA (a := r) (b := a) (rankOneMatrix psi) =
        A * Matrix.conjTranspose A := by
    simpa [A] using
      partialTraceA_rankOneMatrix_eq_rankOneAmplitudeMatrix_mul_conjTranspose psi
  have hConjTransposeMul :
      Matrix.conjTranspose AT * AT =
        Matrix.transpose (A * Matrix.conjTranspose A) := by
    ext i j
    simp [A, AT, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      mul_comm]
  rw [psdTracePower_eq_sum_eigenvalues_rpow,
    psdTracePower_eq_sum_eigenvalues_rpow]
  have hChar :
      Polynomial.X ^ Fintype.card a *
          (partialTraceB (a := r) (b := a) (rankOneMatrix psi)).charpoly =
        Polynomial.X ^ Fintype.card r *
          (partialTraceA (a := r) (b := a) (rankOneMatrix psi)).charpoly := by
    rw [hLeft, hRight]
    have hComm :=
      Matrix.charpoly_mul_comm' (A := AT) (B := Matrix.conjTranspose AT)
    rw [hConjTransposeMul, Matrix.charpoly_transpose] at hComm
    simpa [A, AT, Matrix.mul_assoc] using hComm
  have hP :
      (partialTraceB (a := r) (b := a) (rankOneMatrix psi)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ :
      (partialTraceA (a := r) (b := a) (rankOneMatrix psi)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hRoot :=
    Matrix.roots_re_rpow_sum_eq_of_X_pow_mul_eq (p := p) hp hP hQ hChar
  have hRootsLeft :=
    (partialTraceB_posSemidef (rankOneMatrix_pos psi)).isHermitian.roots_charpoly_eq_eigenvalues
  have hRootsRight :=
    (partialTraceA_posSemidef (rankOneMatrix_pos psi)).isHermitian.roots_charpoly_eq_eigenvalues
  rw [hRootsLeft, hRootsRight] at hRoot
  simpa using hRoot

/-- The two partial traces of an arbitrary finite-dimensional rank-one
bipartite operator have equal PSD Schatten `p` expressions. -/
theorem psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
    (psi : Prod r a → ℂ) (p : SchattenOrder) :
    psdSchattenPNorm
        (partialTraceB (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceB_posSemidef (rankOneMatrix_pos psi)) p =
      psdSchattenPNorm
        (partialTraceA (a := r) (b := a) (rankOneMatrix psi))
        (partialTraceA_posSemidef (rankOneMatrix_pos psi)) p := by
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression] using
    congrArg (fun x : ℝ => Real.rpow x (1 / (p : Real)))
      (psdTracePower_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
        psi p.property)

namespace PureVector

/-- The two marginals of a rank-one bipartite pure operator have equal positive
power traces. -/
theorem psdTracePower_marginalA_eq_marginalB
    (Ψ : PureVector (Prod r a)) {p : ℝ} (hp : 0 < p) :
    psdTracePower
        (partialTraceB (a := r) (b := a) (rankOneMatrix Ψ.amp))
        (partialTraceB_posSemidef (rankOneMatrix_pos Ψ.amp)) p =
      psdTracePower
        (partialTraceA (a := r) (b := a) (rankOneMatrix Ψ.amp))
        (partialTraceA_posSemidef (rankOneMatrix_pos Ψ.amp)) p :=
  psdTracePower_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix Ψ.amp hp

/-- The two marginals of a rank-one bipartite pure operator have equal PSD
Schatten `p` expressions. -/
theorem psdSchattenPNorm_marginalA_eq_marginalB
    (Ψ : PureVector (Prod r a)) (p : SchattenOrder) :
    psdSchattenPNorm
        (partialTraceB (a := r) (b := a) (rankOneMatrix Ψ.amp))
        (partialTraceB_posSemidef (rankOneMatrix_pos Ψ.amp)) p =
      psdSchattenPNorm
        (partialTraceA (a := r) (b := a) (rankOneMatrix Ψ.amp))
        (partialTraceA_posSemidef (rankOneMatrix_pos Ψ.amp)) p :=
  psdSchattenPNorm_partialTraceB_rankOneMatrix_eq_partialTraceA_rankOneMatrix
    Ψ.amp p

end PureVector

end

end QIT
