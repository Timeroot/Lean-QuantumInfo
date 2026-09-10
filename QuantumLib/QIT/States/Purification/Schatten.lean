/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.Schatten
public import QuantumLib.QIT.States.Purification.Gram

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

private def rankOneAmplitudeMatrix (psi : r × a → ℂ) : Matrix a r ℂ :=
  fun x i => psi (i, x)

omit [Fintype r] [DecidableEq r] [DecidableEq a] in
private theorem traceRight_rankOneMatrix_eq_transpose_rankOneAmplitudeMatrix_mul_conjTranspose
    (psi : r × a → ℂ) :
    Matrix.traceRight (rankOneMatrix psi) =
      Matrix.transpose (rankOneAmplitudeMatrix psi) *
        Matrix.conjTranspose (Matrix.transpose (rankOneAmplitudeMatrix psi)) := by
  ext i j
  simp [Matrix.traceRight, rankOneMatrix_apply, rankOneAmplitudeMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.transpose_apply]

omit [DecidableEq r] [Fintype a] [DecidableEq a] in
private theorem traceLeft_rankOneMatrix_eq_rankOneAmplitudeMatrix_mul_conjTranspose
    (psi : r × a → ℂ) :
    Matrix.traceLeft (rankOneMatrix psi) =
      rankOneAmplitudeMatrix psi * Matrix.conjTranspose (rankOneAmplitudeMatrix psi) := by
  ext x y
  simp [Matrix.traceLeft, rankOneMatrix_apply, rankOneAmplitudeMatrix, Matrix.mul_apply]

/-- The two partial traces of an arbitrary finite-dimensional rank-one
bipartite operator have equal positive power traces. -/
theorem psdTracePower_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
    (psi : r × a → ℂ) {p : ℝ} (hp : 0 < p) :
    psdTracePower
        (Matrix.traceRight (rankOneMatrix psi))
        (traceRight_posSemidef (rankOneMatrix_pos psi)) p =
      psdTracePower
        (Matrix.traceLeft (rankOneMatrix psi))
        (traceLeft_posSemidef (rankOneMatrix_pos psi)) p := by
  let A : Matrix a r ℂ := rankOneAmplitudeMatrix psi
  let AT : Matrix r a ℂ := Matrix.transpose A
  have hLeft :
      Matrix.traceRight (rankOneMatrix psi) =
        AT * Matrix.conjTranspose AT := by
    simpa [A, AT] using
      traceRight_rankOneMatrix_eq_transpose_rankOneAmplitudeMatrix_mul_conjTranspose psi
  have hRight :
      Matrix.traceLeft (rankOneMatrix psi) =
        A * Matrix.conjTranspose A := by
    simpa [A] using
      traceLeft_rankOneMatrix_eq_rankOneAmplitudeMatrix_mul_conjTranspose psi
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
          (Matrix.traceRight (rankOneMatrix psi)).charpoly =
        Polynomial.X ^ Fintype.card r *
          (Matrix.traceLeft (rankOneMatrix psi)).charpoly := by
    rw [hLeft, hRight]
    have hComm :=
      Matrix.charpoly_mul_comm' (A := AT) (B := Matrix.conjTranspose AT)
    rw [hConjTransposeMul, Matrix.charpoly_transpose] at hComm
    simpa [A, AT, Matrix.mul_assoc] using hComm
  have hP :
      (Matrix.traceRight (rankOneMatrix psi)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ :
      (Matrix.traceLeft (rankOneMatrix psi)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hRoot :=
    Matrix.roots_re_rpow_sum_eq_of_X_pow_mul_eq (p := p) hp hP hQ hChar
  have hRootsLeft :=
    (traceRight_posSemidef (rankOneMatrix_pos psi)).isHermitian.roots_charpoly_eq_eigenvalues
  have hRootsRight :=
    (traceLeft_posSemidef (rankOneMatrix_pos psi)).isHermitian.roots_charpoly_eq_eigenvalues
  rw [hRootsLeft, hRootsRight] at hRoot
  simpa using hRoot

/-- The two partial traces of an arbitrary finite-dimensional rank-one
bipartite operator have equal PSD Schatten `p` expressions. -/
theorem psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
    (psi : r × a → ℂ) (p : SchattenOrder) :
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix psi))
        (traceRight_posSemidef (rankOneMatrix_pos psi)) p =
      psdSchattenPNorm
        (Matrix.traceLeft (rankOneMatrix psi))
        (traceLeft_posSemidef (rankOneMatrix_pos psi)) p := by
  simpa [psdSchattenPNorm, Internal.psdSchattenExpression] using
    congrArg (fun x : ℝ => Real.rpow x (1 / (p : ℝ)))
      (psdTracePower_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
        psi p.property)

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v
variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

/-- The two marginals of a rank-one bipartite pure operator have equal positive
power traces. -/
theorem psdTracePower_traceRight_eq_traceLeft
    (Ψ : Ket (r × a)) {p : ℝ} (hp : 0 < p) :
    psdTracePower
        (Matrix.traceRight (rankOneMatrix Ψ.vec))
        (traceRight_posSemidef (rankOneMatrix_pos Ψ.vec)) p =
      psdTracePower
        (Matrix.traceLeft (rankOneMatrix Ψ.vec))
        (traceLeft_posSemidef (rankOneMatrix_pos Ψ.vec)) p :=
  psdTracePower_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix Ψ.vec hp

/-- The two marginals of a rank-one bipartite pure operator have equal PSD
Schatten `p` expressions. -/
theorem psdSchattenPNorm_traceRight_eq_traceLeft
    (Ψ : Ket (r × a)) (p : SchattenOrder) :
    psdSchattenPNorm
        (Matrix.traceRight (rankOneMatrix Ψ.vec))
        (traceRight_posSemidef (rankOneMatrix_pos Ψ.vec)) p =
      psdSchattenPNorm
        (Matrix.traceLeft (rankOneMatrix Ψ.vec))
        (traceLeft_posSemidef (rankOneMatrix_pos Ψ.vec)) p :=
  psdSchattenPNorm_traceRight_rankOneMatrix_eq_traceLeft_rankOneMatrix
    Ψ.vec p

end

end Ket

namespace QIT
noncomputable section

universe u v
variable {r : Type u} {a : Type v}
variable [Fintype r] [DecidableEq r] [Fintype a] [DecidableEq a]

end

end QIT
