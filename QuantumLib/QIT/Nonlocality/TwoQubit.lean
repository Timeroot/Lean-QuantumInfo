/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Entanglement.MaximallyEntangled
public import QuantumLib.QIT.States.Purification.ReferenceIsometry

/-!
# Two-qubit primitives

Concrete two-qubit objects used by Bell and certification formalizations.
The computational-basis convention is `false = |0>` and `true = |1>`.
The Pauli `X` and `Z` matrices follow [Wilde2011Qst,
qit-notes.tex:3768-3816]. The singlet follows [Brunner2013BellNonlocality,
ReviewALL.tex:154-156]. Matrix isometries use the convention `V^H * V = 1`
from [Wilde2011Qst, qit-notes.tex:9000-9023].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder Kronecker

namespace QIT
namespace TwoQubit

universe u v w z

noncomputable section

/-- Pauli `X` on the computational basis `false = |0>`, `true = |1>`. -/
def sigmaX : CMatrix Bool := fun i j =>
  match i, j with
  | false, false => 0
  | false, true => 1
  | true, false => 1
  | true, true => 0

/-- Pauli `Z` on the computational basis `false = |0>`, `true = |1>`. -/
def sigmaZ : CMatrix Bool := fun i j =>
  match i, j with
  | false, false => 1
  | false, true => 0
  | true, false => 0
  | true, true => -1

/-- Pauli `X` is Hermitian. -/
theorem sigmaX_isHermitian : sigmaX.IsHermitian := by
  ext i j
  cases i <;> cases j <;> norm_num [sigmaX, Matrix.conjTranspose]

/-- Pauli `Z` is Hermitian. -/
theorem sigmaZ_isHermitian : sigmaZ.IsHermitian := by
  ext i j
  cases i <;> cases j <;> norm_num [sigmaZ, Matrix.conjTranspose]

/-- Pauli `X` squares to the identity. -/
theorem sigmaX_mul_self : sigmaX * sigmaX = 1 := by
  ext i j
  cases i <;> cases j <;> norm_num [sigmaX, Matrix.mul_apply]

/-- Pauli `Z` squares to the identity. -/
theorem sigmaZ_mul_self : sigmaZ * sigmaZ = 1 := by
  ext i j
  cases i <;> cases j <;> norm_num [sigmaZ, Matrix.mul_apply]

/-- The scalar `1 / sqrt 2`, embedded in `ℂ`. -/
def invSqrtTwo : ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The square of `1 / sqrt 2` is `1 / 2`. -/
theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  norm_num [invSqrtTwo, Complex.ext_iff]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

@[simp]
theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

/-- The singlet normalization scalar is fixed by complex conjugation. -/
theorem invSqrtTwo_mul_starRingEnd_invSqrtTwo :
    invSqrtTwo * (starRingEnd ℂ) invSqrtTwo = (1 / 2 : ℂ) := by
  change invSqrtTwo * star invSqrtTwo = (1 / 2 : ℂ)
  rw [star_invSqrtTwo, invSqrtTwo_mul_self]

/-- Amplitudes of the singlet `( |01> - |10> ) / sqrt 2`. -/
def singletAmp : Bool × Bool → ℂ
  | (false, true) => invSqrtTwo
  | (true, false) => -invSqrtTwo
  | _ => 0

/-- Density matrix of the two-qubit singlet. -/
def singletMatrix : CMatrix (Bool × Bool) :=
  rankOneMatrix singletAmp

/-- The singlet amplitude vector is trace-normalized. -/
theorem singlet_trace_rankOne_eq_one :
    (rankOneMatrix singletAmp).trace = 1 := by
  rw [rankOneMatrix_trace]
  change (∑ x : Bool × Bool, singletAmp x * star (singletAmp x)) = 1
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [singletAmp]
  change invSqrtTwo * star invSqrtTwo + invSqrtTwo * star invSqrtTwo = 1
  rw [star_invSqrtTwo, invSqrtTwo_mul_self]
  norm_num

/-- The singlet as a normalized ket. -/
def singletKet : Ket (Bool × Bool) :=
  Ket.ofRankOne singletAmp singlet_trace_rankOne_eq_one

/-- The singlet as a density state. -/
def singletState : MState (Bool × Bool) :=
  singletKet.state

/-- The singlet's Alice marginal is maximally mixed. -/
theorem singletKet_traceRight :
    singletKet.state.traceRight = (MState.uniform : MState Bool) := by
  apply MState.ext
  ext i j
  cases i <;> cases j <;>
  all_goals
    simp [Matrix.traceRight, singletKet, singletAmp]
  all_goals
    try rw [invSqrtTwo_mul_starRingEnd_invSqrtTwo]
  all_goals
    norm_num

/-- The singlet's Bob marginal is maximally mixed. -/
theorem singletKet_traceLeft :
    singletKet.state.traceLeft = (MState.uniform : MState Bool) := by
  apply MState.ext
  ext i j
  cases i <;> cases j <;>
  all_goals
    simp [Matrix.traceLeft, singletKet, singletAmp]
  all_goals
    try rw [invSqrtTwo_mul_starRingEnd_invSqrtTwo]
  all_goals
    norm_num

/-- The two-qubit singlet is maximally entangled. -/
theorem singletKet_isMaximallyEntangled :
    singletKet.IsMaximallyEntangled := by
  apply Ket.HasMaximallyMixedMarginals.isMaximallyEntangled
  constructor
  · exact singletKet_traceRight
  · exact singletKet_traceLeft

/-- A pair of local reference isometries acting on the two sides of a bipartite state. -/
structure LocalIsometry (a : Type u) (a' : Type v) (b : Type w) (b' : Type z)
    [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
    [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b'] where
  /-- The isometry acting on Alice's side. -/
  alice : ReferenceIsometry a a'
  /-- The isometry acting on Bob's side. -/
  bob : ReferenceIsometry b b'

namespace LocalIsometry

variable {a : Type u} {a' : Type v} {b : Type w} {b' : Type z}
variable [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
variable [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']

variable (V : LocalIsometry a a' b b')

/-- Product matrix for the local isometry `V_A tensor V_B`. -/
def matrix : Matrix (a' × b') (a × b) ℂ :=
  V.alice.matrix ⊗ₖ V.bob.matrix

/-- The product of two local isometries is an isometry. -/
theorem matrix_isometry :
    Matrix.conjTranspose V.matrix * V.matrix = 1 := by
  change Matrix.conjTranspose (V.alice.matrix ⊗ₖ V.bob.matrix) *
      (V.alice.matrix ⊗ₖ V.bob.matrix) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    V.alice.isometry, V.bob.isometry, Matrix.one_kronecker_one]

/-- Apply a local isometry to a bipartite matrix. -/
def applyMatrix (rho : CMatrix (a × b)) : CMatrix (a' × b') :=
  V.matrix * rho * Matrix.conjTranspose V.matrix

/-- Applying a local isometry to a density state preserves positivity and trace. -/
def applyState (rho : MState (a × b)) : MState (a' × b') := .ofMatrix
  (matrix := V.applyMatrix rho.m)
  (pos := rho.psd.mul_mul_conjTranspose_same V.matrix)
  (trace_eq_one := by
    rw [applyMatrix, Matrix.trace_mul_cycle, V.matrix_isometry, Matrix.one_mul, rho.tr'])

@[simp]
theorem applyState_matrix (rho : MState (a × b)) :
    (V.applyState rho).m = V.applyMatrix rho.m :=
  MState.matrix_ofMatrix _ _ _

end LocalIsometry

end

end TwoQubit
end QIT
