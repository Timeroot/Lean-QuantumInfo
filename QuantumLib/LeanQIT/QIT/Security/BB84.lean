/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.State
public import QIT.Core.Pure
public import QIT.Nonlocality.TwoQubit
public import QIT.Measurements.Projective
public import QIT.Core.POVMProbability

/-!
# BB84 registers and protocol types

BB84 bit and basis registers for the prepare-and-measure protocol, following
[Renner2005QkdSecurity, main.tex:677-702]. The qubit system is `Bool`, reusing
the Pauli matrices from `QIT.Nonlocality.TwoQubit`.
-/

@[expose] public section

noncomputable section

namespace QIT.Security.BB84

/-- A classical bit. -/
abbrev Bit := Bool

/-- A basis choice: false = rectilinear (Z), true = diagonal (Hadamard, X). -/
abbrev Basis := Bool

/-- A qubit system for BB84. -/
abbrev Qubit := Bool

/-- |0> amplitude. -/
def computationalZero : Qubit -> Complex := fun
  | false => 1
  | true => 0

/-- |1> amplitude. -/
def computationalOne : Qubit -> Complex := fun
  | false => 0
  | true => 1

/-- |+> = (|0> + |1>)/sqrt(2). -/
def hadamardPlus : Qubit -> Complex := fun
  | false => TwoQubit.invSqrtTwo
  | true => TwoQubit.invSqrtTwo

/-- |-> = (|0> - |1>)/sqrt(2). -/
def hadamardMinus : Qubit -> Complex := fun
  | false => TwoQubit.invSqrtTwo
  | true => -TwoQubit.invSqrtTwo

/-- Prepare a BB84 state amplitude from (bit, basis). -/
def prepareAmp : Bit -> Basis -> Qubit -> Complex
  | false, false => computationalZero
  | true, false => computationalOne
  | false, true => hadamardPlus
  | true, true => hadamardMinus

/-- The squared modulus of the Hadamard amplitude. -/
@[simp]
theorem invSqrtTwo_mul_star_invSqrtTwo :
    TwoQubit.invSqrtTwo * star TwoQubit.invSqrtTwo = (1 / 2 : Complex) := by
  rw [TwoQubit.star_invSqrtTwo, TwoQubit.invSqrtTwo_mul_self]

/-- The squared modulus of the Hadamard amplitude, with conjugate first. -/
@[simp]
theorem star_invSqrtTwo_mul_invSqrtTwo :
    star TwoQubit.invSqrtTwo * TwoQubit.invSqrtTwo = (1 / 2 : Complex) := by
  rw [TwoQubit.star_invSqrtTwo, TwoQubit.invSqrtTwo_mul_self]

/-- The squared modulus of the Hadamard amplitude, conjugate first in `starRingEnd` form. -/
@[simp]
theorem starRingEnd_invSqrtTwo_mul_invSqrtTwo :
    (starRingEnd ℂ) TwoQubit.invSqrtTwo * TwoQubit.invSqrtTwo = (1 / 2 : Complex) := by
  change star TwoQubit.invSqrtTwo * TwoQubit.invSqrtTwo = (1 / 2 : Complex)
  rw [TwoQubit.star_invSqrtTwo, TwoQubit.invSqrtTwo_mul_self]

/-- Squared norm trace term for a Bool-indexed amplitude. -/
def selfOverlap (psi : Qubit -> Complex) : Complex :=
  psi ⬝ᵥ fun i => star (psi i)

/-- Born-rule correctness: each BB84 preparation amplitude is normalized.

[Renner2005QkdSecurity, main.tex:677-702] -/
theorem prepare_normalized (bit : Bit) (basis : Basis) :
    selfOverlap (prepareAmp bit basis) = 1 := by
  cases bit <;> cases basis <;>
    simp [selfOverlap, prepareAmp, computationalZero, computationalOne,
      hadamardPlus, hadamardMinus, dotProduct,
      TwoQubit.invSqrtTwo_mul_starRingEnd_invSqrtTwo] <;> norm_num

/-- The prepare-state as a State. -/
def prepareState (bit : Bit) (basis : Basis) : State Qubit where
  matrix := rankOneMatrix (prepareAmp bit basis)
  pos := rankOneMatrix_pos (prepareAmp bit basis)
  trace_eq_one := by
    simpa [selfOverlap] using prepare_normalized bit basis

/-- Same-basis orthogonality: distinct bits in the same basis give
orthogonal states (<psi|phi> = 0). -/
theorem same_basis_orthogonal (basis : Basis) :
    star (prepareAmp false basis false) * (prepareAmp true basis false) +
    star (prepareAmp false basis true) * (prepareAmp true basis true) = 0 := by
  cases basis <;>
    simp [prepareAmp, computationalZero, computationalOne,
      hadamardPlus, hadamardMinus, TwoQubit.invSqrtTwo_mul_self,
      TwoQubit.star_invSqrtTwo]

/-- The projective effect for one BB84 basis/outcome. -/
def measurementEffect (basis : Basis) (outcome : Bit) : CMatrix Qubit :=
  rankOneMatrix (prepareAmp outcome basis)

/-- The BB84 projective measurement in the requested basis. -/
def projectiveMeasurement (basis : Basis) : ProjectiveMeasurement Bit Qubit where
  effects := measurementEffect basis
  isHermitian := by
    intro outcome
    exact rankOneMatrix_isHermitian (prepareAmp outcome basis)
  idempotent := by
    intro outcome
    ext i j
    cases basis <;> cases outcome <;> cases i <;> cases j <;>
      simp [measurementEffect, prepareAmp, computationalZero, computationalOne,
        hadamardPlus, hadamardMinus, Matrix.mul_apply,
        TwoQubit.invSqrtTwo_mul_self,
        TwoQubit.invSqrtTwo_mul_starRingEnd_invSqrtTwo] <;> norm_num
  orthogonal := by
    intro i j hij
    ext r c
    cases basis <;> cases i <;> cases j <;> cases r <;> cases c <;>
      simp_all [measurementEffect, prepareAmp, computationalZero, computationalOne,
        hadamardPlus, hadamardMinus, Matrix.mul_apply]
  sum_eq_one := by
    ext i j
    cases basis <;> cases i <;> cases j <;>
      simp [measurementEffect, prepareAmp, computationalZero, computationalOne,
        hadamardPlus, hadamardMinus, TwoQubit.invSqrtTwo_mul_self] <;> norm_num

@[simp]
theorem projectiveMeasurement_effects (basis : Basis) (outcome : Bit) :
    (projectiveMeasurement basis).effects outcome = measurementEffect basis outcome :=
  rfl

/-- In the matched basis, the Born-rule trace for Alice's bit is one. -/
theorem matched_basis_trace_self (bit basis : Bit) :
    Complex.re (((prepareState bit basis).matrix * measurementEffect basis bit).trace) = 1 := by
  cases bit <;> cases basis <;>
    simp [prepareState, measurementEffect, prepareAmp, computationalZero, computationalOne,
      hadamardPlus, hadamardMinus, Matrix.mul_apply, Matrix.trace,
      TwoQubit.invSqrtTwo_mul_starRingEnd_invSqrtTwo] <;> norm_num

/-- In the matched basis, the Born-rule trace for the complementary bit is zero. -/
theorem matched_basis_trace_compl (bit basis : Bit) :
    Complex.re (((prepareState bit basis).matrix * measurementEffect basis (!bit)).trace) = 0 := by
  cases bit <;> cases basis <;>
    simp [prepareState, measurementEffect, prepareAmp, computationalZero, computationalOne,
      hadamardPlus, hadamardMinus, Matrix.mul_apply, Matrix.trace]

/-- Measuring a BB84 state in its preparation basis recovers Alice's bit with probability one.

[Renner2005QkdSecurity, main.tex:677-702] -/
theorem matched_basis_prob_self (bit basis : Bit) :
    ((projectiveMeasurement basis).toPOVM.prob (prepareState bit basis) bit : ℝ) = 1 := by
  rw [POVM.prob_eq_trace_re]
  exact matched_basis_trace_self bit basis

/-- Measuring a BB84 state in its preparation basis never returns the complementary bit. -/
theorem matched_basis_prob_compl (bit basis : Bit) :
    ((projectiveMeasurement basis).toPOVM.prob (prepareState bit basis) (!bit) : ℝ) = 0 := by
  rw [POVM.prob_eq_trace_re]
  exact matched_basis_trace_compl bit basis

/-- A BB84 round record. -/
structure Round where
  aliceBit : Bit
  aliceBasis : Basis
  bobBasis : Basis
  bobOutcome : Bit

/-- Sifted output: keep a key bit, or abort. -/
inductive SiftOutput where
  | keep : Bit -> SiftOutput
  | abort : SiftOutput
deriving DecidableEq, Repr

/-- Extract the kept bit, if the round was retained after sifting. -/
def SiftOutput.toOption : SiftOutput -> Option Bit
  | SiftOutput.keep bit => some bit
  | SiftOutput.abort => none

@[simp]
theorem SiftOutput.toOption_keep (bit : Bit) :
    (SiftOutput.keep bit).toOption = some bit :=
  rfl

@[simp]
theorem SiftOutput.toOption_abort :
    SiftOutput.abort.toOption = none :=
  rfl

/-- Predicate for the explicit abort output. -/
def SiftOutput.isAbort : SiftOutput -> Bool
  | SiftOutput.abort => true
  | SiftOutput.keep _ => false

@[simp]
theorem SiftOutput.isAbort_keep (bit : Bit) :
    (SiftOutput.keep bit).isAbort = false :=
  rfl

@[simp]
theorem SiftOutput.isAbort_abort :
    SiftOutput.abort.isAbort = true :=
  rfl

/-- Process a single round. -/
def processRound (r : Round) : SiftOutput :=
  if r.aliceBasis = r.bobBasis then SiftOutput.keep r.bobOutcome
  else SiftOutput.abort

/-- Matched bases keep Bob's outcome in the sifted transcript. -/
theorem processRound_eq_keep_of_basis_eq (r : Round) (h : r.aliceBasis = r.bobBasis) :
    processRound r = SiftOutput.keep r.bobOutcome := by
  simp [processRound, h]

/-- Mismatched bases produce the explicit abort output for that round. -/
theorem processRound_eq_abort_of_basis_ne (r : Round) (h : r.aliceBasis ≠ r.bobBasis) :
    processRound r = SiftOutput.abort := by
  simp [processRound, h]

/-- Process every round into an explicit keep/abort output. -/
def processRounds (rounds : List Round) : List SiftOutput :=
  rounds.map processRound

/-- Keep only the bits retained by sifting. -/
def keptBits (rounds : List Round) : List Bit :=
  (processRounds rounds).filterMap SiftOutput.toOption

/-- Count the explicit abort outputs in a list of processed rounds. -/
def abortCount (rounds : List Round) : Nat :=
  ((processRounds rounds).filter fun output => output.isAbort).length

/-- Sift a single tuple of announced bases and Bob's outcome. -/
def siftTriple (aliceBasis bobBasis : Basis) (bobOutcome : Bit) : Option Bit :=
  (processRound
    { aliceBit := false
      aliceBasis := aliceBasis
      bobBasis := bobBasis
      bobOutcome := bobOutcome }).toOption

/-- Sift a list of BB84 rounds to retained key bits. -/
def sift (rounds : List Round) : List Bit :=
  keptBits rounds

/-- A sifted transcript: the list of kept bits plus abort count. -/
structure Transcript where
  siftedBits : List Bit
  outputs : List SiftOutput
  aborts : Nat
  roundsProcessed : Nat

/-- Build a transcript from a list of rounds. -/
def buildTranscript (rounds : List Round) : Transcript :=
  { siftedBits := keptBits rounds
    outputs := processRounds rounds
    aborts := abortCount rounds
    roundsProcessed := rounds.length }

@[simp]
theorem buildTranscript_siftedBits (rounds : List Round) :
    (buildTranscript rounds).siftedBits = keptBits rounds :=
  rfl

@[simp]
theorem buildTranscript_outputs (rounds : List Round) :
    (buildTranscript rounds).outputs = processRounds rounds :=
  rfl

@[simp]
theorem buildTranscript_aborts (rounds : List Round) :
    (buildTranscript rounds).aborts = abortCount rounds :=
  rfl

@[simp]
theorem buildTranscript_roundsProcessed (rounds : List Round) :
    (buildTranscript rounds).roundsProcessed = rounds.length :=
  rfl

/-!
## Prepare-measure to entanglement-based route

The declarations above provide the prepare-and-measure side of BB84:
state preparation, the two projective measurements, ideal matched-basis
Born-rule correctness, and a classical sifting transcript with explicit aborts.
The future entanglement-based route still needs an EPR-pair formulation,
Alice-side measurement equivalence, and a security proof on the
entanglement-based side.
-/

end QIT.Security.BB84
