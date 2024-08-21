import Mathlib.Analysis.SpecialFunctions.Log.Base

import QuantumInfo.Finite.Entropy
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Distance

--Quantum capacities... https://cs.uwaterloo.ca/~watrous/TQI/TQI.8.pdf
-- * Quantum 1-shot capacity
-- * Quantum capacity -- LSD theorem
-- * Entanglement-assisted classical capacity
-- * Qss
-- * Holevo capacity, Holevo χ, Holevo–Schumacher–Westmoreland theorem
-- * Entanglement-assisted Holevo capacity
-- * Entanglement-assisted quantum capacity
-- * One- and two-way distillable entanglement
-- Nonadditivity, superactivation

/- Quantum Capacity

Quantum capacity is defined in different reference works in at least five meaningfully different ways:

(1) https://www.uio.no/studier/emner/matnat/math/MAT4430/v23/timeplan/lectureblup.pdf, Defn 20.3.

Defines the notion of "(n, m, δ)-coding scheme", a code for m qubits in n copies of the channel, with diamond-norm distance of δ from the identity channel. Then a rate R is "achievable" if there is a sequence of coding schemes that converge m/n -> R and δ -> 0. The set of achieveable rates is a closed interval, and the capacity is the maximum of this interval.

(2) https://cs.uwaterloo.ca/~watrous/TQI/TQI.8.pdf, Defn 8.42.

Watrous doesn't use the word "coding scheme", but rather define "emulating" (8.1) an "ε-approximation" (8.2) of the identity. This is equivalent to the coding scheme and diamond norm part. Then a rate R is "achievable" if, for every δ>0, there is a k:ℕ such that k < n implies the existence of a (n, floor(R*n), δ)-coding scheme. Now the set of achievable rates may be an open or closed interval, and the capacity is the supremum of this interval (not the maximum, since an open interval has no maximum).

(3) Works like https://arxiv.org/pdf/1007.2855 (equation 3) and https://arxiv.org/pdf/1801.02019 (equation 186) define the quantum capacity of C as $Q(C) = lim_n 1/n * Q^{(1)}(C ^ {⊗n})$, where $Q^{(1)}$ is the quantum coherent information (or "one-shot channel capacity"), and so it is the average coherent information achieved across n copies of the channel, in the large-n limit. This definition makes the LSD theorem (which stats that $Q ≥ Q^{(1)}$) actually entirely trivial, as it requires only the fact that $Q^{(1)}$ is superadditive.

(4) https://arxiv.org/pdf/quant-ph/0304127 (Section 5) and https://arxiv.org/pdf/quant-ph/9809010 specifically distinguish between "subspace transmission", "entanglement transmission", and "entanglement generation" capabilities of the channel. The fact that all three are equal is then a theorem. Option (4), subspace transsmission capacity, is like option (1) above, but instead of the channel having diamond norm at most δ from the identity channel, we require that the channel has fidelity at least 1-δ on all inputs. Converging in fidelity is surely equivalent to converging in diamond norm, but the precise bounds are not obvious. (4) also differs from (1) and (2) in that it has an arbitrary dimension input space, instead of specifically a 2^n-dimensional space of qubits. arxiv:9809010 specifically requires a sequence of codes whose limiting fidelity is 1 and rate is R; arxiv:0304127 doesn't actually precisely say.

(5) "Entanglement transmission" asks for a high-entropy state (thus, a large subspace dimension) that can be transmitted through the channel with a high "entanglement fidelity". See equation (52) in arxiv:0304127. The rate achieved is the von Neumann entropy of the state, the set of achievable rates are closed, and the rate of the channel is the maximum.

(6) "Entanglement generation" changes the task from coding. Instead we need a bipartite state ρ_AB on a Hilbert space of dimension κ, of which the left half goes through the encoder, channel, and decoder. The fidelity between the result C(ρ) and the maximally entangled state must be at least 1-ε. The rates are (1/n)*(log κ), achievable if for all δ and sufficiently large n (etc. - like option (2)), and we take the supremum.

Note: Option (6) is what Devetak, in arxiv:0304127, actually proves the LSD theorem for. Theorem 5 in that reference. (4), (5), and (6) are proven equal.

(7) Wilde's book also of "coding scheme", but defines it in terms of entanglement generation and the logarithm of the dimension of the space. Instead of fidelity preserved in the entanglement, it's the trace norm. He effectively defines it by supremum, although he doesn't need to use the word, giving an equivalent δ/ε definition for coding schemes. He then takes supremum (even though maximum would work as well -- the capacity is itself an achievable rate by his definition). In this way, it combines aspects of definitions (1), (2), and (4). He gives as an exercise showing that small trace norm error of transmitted states implies a small diamond norm error from the identity.

----

To capture the idea of "quantum capacity", and some other idea that turns out to be equivalent, (1), (2), or (5) seems best. The definitions (1) and (2) seem to be the more recently popular ones. Between those two, choosing "supremum" or "maximum", the supremum seems shorter to state in a definition (as it doesn't require proving closure); indeed Mathlib has no notion of "max real" as a function, only a supremum which can also be shown to be in the set. But the definition in (2) of "For every δ>0, there is a k:ℕ such that k < n implies the existence of a (...)-coding scheme" is cleaner work with as a way to directly construct or extract codes, as opposed to limits of sequences of codes. And finally, the notions of "emulate" and "approximate" seem useful for defining it more elegantly. So, final definition:

A channel A `emulates` another channel B if there are D and E such that D∘A∘E = B.

A channel A `εApproximates` channel B (of the same dimensions) if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.

A channel A `achievesRate` R:ℝ if for every ε>0, n copies of A emulates some channel B such that log2(dimout(B))/n ≥ R, and that B is εApproximately the identity.

The `QuantumCapacity` of the channel A is the supremum of the achievable rates, i.e. `sSup { R : ℝ | achievesRate A R }`.

The most basic facts:
 * Every channel emulates itself.
 * If A emulates B and B emulates C, then A emulates C. (That is, emulation is an ordering.)
 * `εApproximates A B ε` is equivalent to the existence of some δ (depending ε and dims(A)) so that |A-B| has diamond norm at most δ, and δ→0 as ε→0.
 * Every channel achievesRate 0. So, the set of achievable rates is Nonempty.
 * If a channel achievesRate R₁, it also every achievesRate R₂ every R₂ ≤ R₁, i.e. it is an interval extending left towards -∞. Achievable rates are `¬BddBelow`.
 * A channel C : dimX → dimY cannot achievesRate R with `R > log2(min(dimX, dimY))`. Thus, the interval is `BddAbove`.

The nice lemmas we would want:
 * Capacity of a replacement channel is zero.
 * Capacity of an identity channel is `log2(D)`.
 * Capacity is superadditive under tensor products. (That is, at least additive. Showing that it isn't _exactly_ additive, unlike classical capacity which is additive, is a much harder task.)
 * Capacity of a kth tensor power is exactly k times the capacity of the original channel.
 * Capacity does not decrease under tensor sums.
 * Capacity does not increase under composition.

Then, we should show that our definition is equivalent to some above. Most, except (3), should be not too hard to prove.

Then the LSD theorem establishes that the single-copy coherent information is a lower bound.

Finally, showing that the n-copy coherent information converges to the capacity.

-/

namespace CPTPMap

variable {d₁ d₂ d₃ d₄ d₅ d₆ : Type*}
variable [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype d₄] [Fintype d₅] [Fintype d₆] [DecidableEq d₁]

variable [DecidableEq d₂] [DecidableEq d₃] [DecidableEq d₄] in
/--
A channel Λ₁ `Emulates` another channel Λ₂ if there are D and E such that D∘Λ₁∘E = Λ₂.
-/
def emulates (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) : Prop :=
  ∃ (E : CPTPMap d₃ d₁) (D : CPTPMap d₂ d₄), D.compose (Λ₁.compose E) = Λ₂

/--
A channel A `εApproximates` channel B of the same dimensions if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.
-/
def εApproximates (A B : CPTPMap d₁ d₂) (ε : ℝ) : Prop :=
  ∀ (ρ : MState d₁), (A ρ).Fidelity (B ρ) ≥ 1-ε

variable [DecidableEq d₂] in
/--
A channel A `AchievesRate` R:ℝ if for every ε>0, some n copies of A emulates a channel B such that log2(dimout(B))/n ≥ R, and that B εApproximates the identity channel.
-/
def achievesRate (A : CPTPMap d₁ d₂) (R : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ (n : ℕ) (dimB : ℕ) (B : CPTPMap (Fin dimB) (Fin dimB)),
      (CPTPMap.fin_n_prod (fun (_ : Fin n) ↦ A)).emulates B ∧
      Real.logb 2 dimB ≥ R*n ∧
      B.εApproximates CPTPMap.id ε

variable [DecidableEq d₂] in
noncomputable def QuantumCapacity (A : CPTPMap d₁ d₂) : ℝ :=
  sSup { R : ℝ | achievesRate A R }

section emulates
variable [DecidableEq d₂] [DecidableEq d₃] [DecidableEq d₄] [DecidableEq d₅] [DecidableEq d₆]

/-- Every quantum channel emulates itself. -/
theorem emulates_self (Λ : CPTPMap d₁ d₂) : Λ.emulates Λ :=
  ⟨CPTPMap.id, CPTPMap.id, by simp⟩

/-- If a quantum channel A emulates B, and B emulates C, then A emulates C. -/
theorem emulates_trans (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) (Λ₃ : CPTPMap d₅ d₆)
  (h₁₂ : Λ₁.emulates Λ₂) (h₂₃ : Λ₂.emulates Λ₃) : Λ₁.emulates Λ₃ := by
  obtain ⟨E₁, D₁, hED₁⟩ := h₁₂
  obtain ⟨E₂, D₂, hED₂⟩ := h₂₃
  exact ⟨E₁.compose E₂, D₂.compose D₁, by simp [← hED₁, ← hED₂, compose_assoc]⟩

end emulates

section εApproximates

/-- Every quantum channel perfectly approximates itself, that is, `εApproximates` with `ε = 0`. -/
theorem εApproximates_self (Λ : CPTPMap d₁ d₂) : Λ.εApproximates Λ 0 :=
  fun ρ ↦ ((Λ ρ).fidelity_self_eq_one.trans (sub_zero 1).symm).ge

/-- If a quantum channel A approximates B with ε₀, it also approximates B with all larger ε₁. -/
theorem εApproximates_monotone {A B : CPTPMap d₁ d₂} {ε₀ : ℝ} (h : A.εApproximates B ε₀)
    {ε₁ : ℝ} (h₂ : ε₀ ≤ ε₁) : A.εApproximates B ε₁ :=
  fun ρ ↦ (tsub_le_tsub_left h₂ 1).trans (h ρ)

end εApproximates

section achievesRate
variable [DecidableEq d₂]

/-- Every quantum channel achieves a rate of zero. -/
theorem achievesRate_0 (Λ : CPTPMap d₁ d₂) : Λ.achievesRate 0 := by
  intro ε hε
  let _ : Nonempty (Fin 1) := Fin.pos_iff_nonempty.mp Nat.one_pos
  let _ : Nonempty (Fin 0 → d₂) := instNonemptyOfInhabited
  use 0, 1, default
  constructor
  · exact ⟨default, default, Unique.eq_default _⟩
  constructor
  · norm_num
  · rw [Unique.eq_default id]
    exact εApproximates_monotone (εApproximates_self default) hε.le

/-- The identity channel on D dimensional space achieves a rate of log2(D). -/
theorem id_achievesRate_log_dim : (id (dIn := d₁)).achievesRate (Real.logb 2 (Fintype.card d₁)) := by
  intro ε hε
  use 1, Fintype.card d₁, id
  constructor
  · sorry--they are equivalent up to permutation
  constructor
  · norm_num
  · exact εApproximates_monotone (εApproximates_self id) hε.le

/-- A channel cannot achieve a rate greater than log2(D), where D is the input dimension. -/
theorem not_achievesRate_gt_log_dim_in (Λ : CPTPMap d₁ d₂) {R : ℝ} (hR : Real.logb 2 (Fintype.card d₁) < R): ¬Λ.achievesRate R := by
  sorry

/-- A channel cannot achieve a rate greater than log2(D), where D is the output dimension. -/
theorem not_achievesRate_gt_log_dim_out (Λ : CPTPMap d₁ d₂) {R : ℝ} (hR : Real.logb 2 (Fintype.card d₂) < R): ¬Λ.achievesRate R := by
  sorry

/-- The achievable rates are a bounded set. -/
theorem BddAbove_achievesRate (Λ : CPTPMap d₁ d₂) : BddAbove {R | Λ.achievesRate R} := by
  use Real.logb 2 (Fintype.card d₁)
  intro R h
  contrapose h
  exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h)

end achievesRate

section capacity
variable [DecidableEq d₂]

/-- Quantum channel capacity is nonnegative. -/
theorem zero_le_QuantumCapacity (Λ : CPTPMap d₁ d₂) : 0 ≤ Λ.QuantumCapacity :=
  le_csSup (BddAbove_achievesRate Λ) (achievesRate_0 Λ)

/-- Quantum channel capacity is at most log2(D), where D is the input dimension. -/
theorem QuantumCapacity_gt_log_dim_in (Λ : CPTPMap d₁ d₂) : Λ.QuantumCapacity ≤ Real.logb 2 (Fintype.card d₁) :=
  Real.sSup_le (by
    intro R h
    contrapose h
    exact not_achievesRate_gt_log_dim_in Λ (lt_of_not_ge h))
  (by
    by_cases h : Nonempty d₁
    · apply Real.logb_nonneg one_lt_two (Nat.one_le_cast.mpr Fintype.card_pos)
    · simp [not_nonempty_iff.mp h])

end capacity
