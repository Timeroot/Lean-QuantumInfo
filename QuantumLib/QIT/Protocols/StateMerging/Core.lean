/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.Protocols.FQSW.Core
public import QuantumLib.QIT.Protocols.LOCC.Core
public import QuantumLib.QIT.States.Geometry.FuchsVdG

/-!
# Operational semantics for quantum state merging

This module formalizes the finite one-way-LOCC protocol contract in the
definition of Horodecki--Oppenheim--Winter state merging.  A protocol acts on
the grouped IID source and an input maximally entangled pair.  Its output,
ideal target, fidelity error, net entanglement rate, and classical rate are
derived from the instrument, conditional Bob channels, and register
cardinalities; none of them is freely assignable.

The source definition and rate convention are in
`swlong.6.2.tex:545-608`.  The equality of the optimal cost with `H(A|B)` is a
separate direct/converse theorem and is not asserted here.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

namespace QIT

universe u v w x y z p q u' v'

noncomputable section

/-- Regroup the block source and input entanglement as local Alice, local Bob,
and inaccessible reference registers. -/
def stateMergingInputEquiv
    (A : Type u) (B : Type v) (R : Type w) (KA : Type x) (KB : Type y) :
    (((A × B) × R) × (KA × KB)) ≃
      (((A × KA) × (B × KB)) × R) where
  toFun t := (((t.1.1.1, t.2.1), (t.1.1.2, t.2.2)), t.1.2)
  invFun t := (((t.1.1.1, t.1.2.1), t.2), (t.1.1.2, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

/-- Regroup the transferred source and output entanglement in the output order
of the one-way LOCC channel, followed by the untouched reference. -/
def stateMergingTargetEquiv
    (A : Type u) (B : Type v) (R : Type w) (LA : Type x) (LB : Type y) :
    (((A × B) × R) × (LA × LB)) ≃
      ((LA × ((A × B) × LB)) × R) where
  toFun t := ((t.2.1, (t.1.1, t.2.2)), t.1.2)
  invFun t := ((t.1.2.1, t.2), (t.1.1, t.1.2.2))
  left_inv := by intro t; rfl
  right_inv := by intro t; rfl

variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- The grouped IID pure source `(A^n B^n) R^n`. -/
def stateMergingBlockSource
    (psi : Ket ((a × b) × r)) (n : ℕ) :
    Ket
      ((TensorPower a n × TensorPower b n) × TensorPower r n) :=
  (psi.tensorPower n).reindex (tensorPowerProdProdEquiv a b r n)

/-- A source-shaped finite block state-merging protocol.

Alice holds `A^n K_A`, Bob holds `B^n K_B`, and the input pair has Schmidt
rank `K = |K_A|`.  The one-way LOCC operation leaves Alice with `L_A` and
gives Bob `B' B^n L_B`, where `B'` has the same basis as `A^n`; the output pair
has rank `L = |L_A|`. -/
structure StateMergingBlockProtocol
    (psi : Ket ((a × b) × r)) (n : ℕ)
    (kA : Type x) (kB : Type y) (lA : Type z) (lB : Type p)
    (outcome : Type q)
    [Fintype kA] [DecidableEq kA] [Nonempty kA]
    [Fintype kB] [DecidableEq kB]
    [Fintype lA] [DecidableEq lA] [Nonempty lA]
    [Fintype lB] [DecidableEq lB]
    [Fintype outcome] [DecidableEq outcome] [Nonempty outcome] where
  /-- The identification of the two halves of the input ebits. -/
  inputEbitPairing : kA ≃ kB
  /-- The identification of the two halves of the output ebits. -/
  outputEbitPairing : lA ≃ lB
  /-- The one-way LOCC operation the protocol performs. -/
  locc :
    OneWayLOCC
      (TensorPower a n × kA)
      lA
      (TensorPower b n × kB)
      ((TensorPower a n × TensorPower b n) × lB)
      outcome

namespace StateMergingBlockProtocol

variable {psi : Ket ((a × b) × r)} {n : ℕ}
variable {kA : Type x} {kB : Type y} {lA : Type z} {lB : Type p}
variable {outcome : Type q}
variable [Fintype kA] [DecidableEq kA] [Nonempty kA]
variable [Fintype kB] [DecidableEq kB]
variable [Fintype lA] [DecidableEq lA] [Nonempty lA]
variable [Fintype lB] [DecidableEq lB]
variable [Fintype outcome] [DecidableEq outcome] [Nonempty outcome]

/-- Decidable equality on the protocol's output register, assembled from the
factor instances so that it is definitionally the product instance. -/
local instance stateMergingOutputDecidableEq :
    DecidableEq
      ((lA × ((TensorPower a n × TensorPower b n) × lB)) ×
        TensorPower r n) :=
  @instDecidableEqProd _ _
    (@instDecidableEqProd _ _ inferInstance
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _
          (tensorPowerDecidableEq n) (tensorPowerDecidableEq n))
        inferInstance))
    (tensorPowerDecidableEq n)

variable (C : StateMergingBlockProtocol psi n kA kB lA lB outcome)

/-- The physical input `psi^n tensor Phi_K`, regrouped as local Alice, local
Bob, and reference systems. -/
def initialState :
    MState
      (((TensorPower a n × kA) × (TensorPower b n × kB)) ×
        TensorPower r n) :=
  ((stateMergingBlockSource psi n).state.prod
      (MState.maximallyEntangled C.inputEbitPairing)).reindex
    (stateMergingInputEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) kA kB)

/-- The output computed by the one-way LOCC operation, tensored with the
identity channel on the inaccessible reference. -/
def outputState :
    MState
      ((lA × ((TensorPower a n × TensorPower b n) × lB)) ×
        TensorPower r n) :=
  (C.locc.toChannel.prod (CPTPOp.id (dIn := TensorPower r n))) C.initialState

/-- The ideal target `Phi_L tensor psi_{B'BR}^n`, expressed in the same output
register order as `outputState`. -/
def targetState :
    MState
      ((lA × ((TensorPower a n × TensorPower b n) × lB)) ×
        TensorPower r n) :=
  ((stateMergingBlockSource psi n).state.prod
      (MState.maximallyEntangled C.outputEbitPairing)).reindex
    (stateMergingTargetEquiv
      (TensorPower a n) (TensorPower b n) (TensorPower r n) lA lB)

/-- Fidelity error `1 - F`, with `F` the repository's squared-fidelity
convention used for the HOW state-merging criterion. -/
def fidelityError : ℝ :=
  1 - C.outputState.squaredFidelity C.targetState

theorem fidelityError_nonneg : 0 ≤ C.fidelityError :=
  sub_nonneg.mpr (MState.squaredFidelity_le_one _ _)

theorem fidelityError_le_iff (epsilon : ℝ) :
    C.fidelityError ≤ epsilon ↔
      1 - epsilon ≤ C.outputState.squaredFidelity C.targetState := by
  unfold fidelityError
  constructor <;> intro h <;> linarith

/-- Net entanglement consumption `(log K - log L) / n`.  This real-valued
quantity is intentionally allowed to be negative. -/
def netEntanglementRate
    (_C : StateMergingBlockProtocol psi n kA kB lA lB outcome) : ℝ :=
  if n = 0 then 0
  else (log2 (Fintype.card kA : ℝ) - log2 (Fintype.card lA : ℝ)) / (n : ℝ)

/-- One-way classical communication rate `log |X| / n`. -/
def classicalCommunicationRate
    (_C : StateMergingBlockProtocol psi n kA kB lA lB outcome) : ℝ :=
  if n = 0 then 0 else log2 (Fintype.card outcome : ℝ) / (n : ℝ)

end StateMergingBlockProtocol

end
end QIT

namespace Ket

noncomputable section

open QIT
universe u v w x y z p q u' v'
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

/-- Achievable net entanglement rate for standard state merging in the sense
of HOW. Every positive rate slack and fidelity-error tolerance is met by
concrete one-way LOCC block protocols at all sufficiently large blocklengths.
No output-ebit-rank growth condition is imposed. -/
def IsAchievableStateMergingRate
    (psi : Ket ((a × b) × r)) (R : ℝ) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (kA : Type x), ∃ (_ : Fintype kA), ∃ (_ : DecidableEq kA),
        ∃ (_ : Nonempty kA),
      ∃ (kB : Type y), ∃ (_ : Fintype kB), ∃ (_ : DecidableEq kB),
      ∃ (lA : Type z), ∃ (_ : Fintype lA), ∃ (_ : DecidableEq lA),
        ∃ (_ : Nonempty lA),
      ∃ (lB : Type p), ∃ (_ : Fintype lB), ∃ (_ : DecidableEq lB),
      ∃ (outcome : Type q), ∃ (_ : Fintype outcome), ∃ (_ : DecidableEq outcome),
        ∃ (_ : Nonempty outcome),
      ∃ C : StateMergingBlockProtocol psi n kA kB lA lB outcome,
        C.netEntanglementRate ≤ R + delta ∧
        C.fidelityError ≤ epsilon

/-- Exponent-restricted state-merging achievability used by the existing HOW
converse. One nonnegative exponent uniformly bounds the output ebit rank over
all tolerances and all sufficiently large selected protocols. -/
def IsAchievableStateMergingRateWithOutputEbitExponent
    (psi : Ket ((a × b) × r)) (R : ℝ) : Prop :=
  ∃ outputEbitExponent : ℝ, 0 ≤ outputEbitExponent ∧
  ∀ delta : ℝ, 0 < delta → ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, n ≥ N →
      ∃ (kA : Type x), ∃ (_ : Fintype kA), ∃ (_ : DecidableEq kA),
        ∃ (_ : Nonempty kA),
      ∃ (kB : Type y), ∃ (_ : Fintype kB), ∃ (_ : DecidableEq kB),
      ∃ (lA : Type z), ∃ (_ : Fintype lA), ∃ (_ : DecidableEq lA),
        ∃ (_ : Nonempty lA),
      ∃ (lB : Type p), ∃ (_ : Fintype lB), ∃ (_ : DecidableEq lB),
      ∃ (outcome : Type q), ∃ (_ : Fintype outcome), ∃ (_ : DecidableEq outcome),
        ∃ (_ : Nonempty outcome),
      ∃ C : StateMergingBlockProtocol psi n kA kB lA lB outcome,
        C.netEntanglementRate ≤ R + delta ∧
        C.fidelityError ≤ epsilon ∧
        log2 (Fintype.card lA : ℝ) ≤ outputEbitExponent * (n : ℝ)

/-- Exponent-restricted achievability implies canonical HOW achievability. -/
theorem IsAchievableStateMergingRateWithOutputEbitExponent.toIsAchievableStateMergingRate
    {psi : Ket ((a × b) × r)} {R : ℝ}
    (hR :
      IsAchievableStateMergingRateWithOutputEbitExponent.{u, v, w, x, y, z, p, q} psi R) :
    IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi R := by
  obtain ⟨_, _, hrestricted⟩ := hR
  intro delta hdelta epsilon hepsilon
  obtain ⟨N, _, hblocks⟩ := hrestricted delta hdelta epsilon hepsilon
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨kA, hkAF, hkAD, hkAN, kB, hkBF, hkBD,
      lA, hlAF, hlAD, hlAN, lB, hlBF, hlBD,
      outcome, houtcomeF, houtcomeD, houtcomeN,
      C, hrate, herror, _⟩ := hblocks n hn
  exact ⟨kA, hkAF, hkAD, hkAN, kB, hkBF, hkBD,
    lA, hlAF, hlAD, hlAN, lB, hlBF, hlBD,
    outcome, houtcomeF, houtcomeD, houtcomeN,
    C, hrate, herror⟩

/-- Standard state-merging cost: the infimum of achievable net entanglement
rates.  No sign restriction is imposed, so negative conditional-entropy
sources can be represented as net entanglement generation. -/
def stateMergingCost (psi : Ket ((a × b) × r)) : ℝ :=
  sInf {R : ℝ |
    Ket.IsAchievableStateMergingRate.{u, v, w, x, y, z, p, q} psi R}

end

end Ket

namespace QIT
noncomputable section

universe u v w x y z p q u' v'
variable {a : Type u} {b : Type v} {r : Type w}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype r] [DecidableEq r]

end

end QIT
