/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Entanglement.MaximallyEntangled
public import QIT.States.Purification.ReferenceIsometry

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

/-- The scalar `1 / sqrt 2`, embedded in `Complex`. -/
def invSqrtTwo : Complex :=
  ((Real.sqrt 2 : ℝ) : Complex)⁻¹

/-- The square of `1 / sqrt 2` is `1 / 2`. -/
theorem invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (1 / 2 : Complex) := by
  norm_num [invSqrtTwo, Complex.ext_iff]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

@[simp]
theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

/-- The singlet normalization scalar is fixed by complex conjugation. -/
theorem invSqrtTwo_mul_starRingEnd_invSqrtTwo :
    invSqrtTwo * (starRingEnd ℂ) invSqrtTwo = (1 / 2 : Complex) := by
  change invSqrtTwo * star invSqrtTwo = (1 / 2 : Complex)
  rw [star_invSqrtTwo, invSqrtTwo_mul_self]

/-- Amplitudes of the singlet `( |01> - |10> ) / sqrt 2`. -/
def singletAmp : Bool × Bool → Complex
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

/-- The singlet as a normalized pure vector. -/
def singletPureVector : PureVector (Bool × Bool) where
  amp := singletAmp
  trace_rankOne_eq_one := singlet_trace_rankOne_eq_one

/-- The singlet as a density state. -/
def singletState : State (Bool × Bool) :=
  singletPureVector.state

/-- The singlet's Alice marginal is maximally mixed. -/
theorem singletPureVector_marginalA :
    singletPureVector.state.marginalA = State.maximallyMixed Bool := by
  apply State.ext
  ext i j
  cases i <;> cases j <;>
  all_goals
    simp [State.marginalA, partialTraceB, singletPureVector, singletAmp,
      State.maximallyMixed, rankOneMatrix_apply]
  all_goals
    try rw [invSqrtTwo_mul_starRingEnd_invSqrtTwo]
  all_goals
    norm_num

/-- The singlet's Bob marginal is maximally mixed. -/
theorem singletPureVector_marginalB :
    singletPureVector.state.marginalB = State.maximallyMixed Bool := by
  apply State.ext
  ext i j
  cases i <;> cases j <;>
  all_goals
    simp [State.marginalB, partialTraceA, singletPureVector, singletAmp,
      State.maximallyMixed, rankOneMatrix_apply]
  all_goals
    try rw [invSqrtTwo_mul_starRingEnd_invSqrtTwo]
  all_goals
    norm_num

/-- The two-qubit singlet is maximally entangled. -/
theorem singletPureVector_isMaximallyEntangled :
    singletPureVector.IsMaximallyEntangled := by
  apply PureVector.HasMaximallyMixedMarginals.isMaximallyEntangled
  constructor
  · exact singletPureVector_marginalA
  · exact singletPureVector_marginalB

/-- A pair of local reference isometries acting on the two sides of a bipartite state. -/
structure LocalIsometry (a : Type u) (a' : Type v) (b : Type w) (b' : Type z)
    [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
    [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b'] where
  alice : ReferenceIsometry a a'
  bob : ReferenceIsometry b b'

namespace LocalIsometry

variable {a : Type u} {a' : Type v} {b : Type w} {b' : Type z}
variable [Fintype a] [DecidableEq a] [Fintype a'] [DecidableEq a']
variable [Fintype b] [DecidableEq b] [Fintype b'] [DecidableEq b']

variable (V : LocalIsometry a a' b b')

/-- Product matrix for the local isometry `V_A tensor V_B`. -/
def matrix : Matrix (a' × b') (a × b) Complex :=
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
def applyState (rho : State (a × b)) : State (a' × b') where
  matrix := V.applyMatrix rho.matrix
  pos := rho.pos.mul_mul_conjTranspose_same V.matrix
  trace_eq_one := by
    rw [applyMatrix, Matrix.trace_mul_cycle, V.matrix_isometry, Matrix.one_mul, rho.trace_eq_one]

@[simp]
theorem applyState_matrix (rho : State (a × b)) :
    (V.applyState rho).matrix = V.applyMatrix rho.matrix :=
  rfl

end LocalIsometry

end

end TwoQubit
end QIT
