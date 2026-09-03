/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Security.Key

/-!
# Key-distillation security scaffold

Definition-level API for Renner's key-distillation security scaffold, following
the distance-from-uniform convention and correctness/secrecy decomposition in
[Renner2005QkdSecurity, main.tex:6704-6718] and
[Renner2005QkdSecurity, main.tex:7427-7443].  The source-facing API uses a
subnormalized successful branch; explicit abort outputs are bridged by success
extraction wrappers.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe u v

noncomputable section

variable {κ : Type u} {e : Type v}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype e] [DecidableEq e]

/-- Two retained key outputs disagree exactly when both parties output keys
and the retained key values differ. -/
def keyPairMismatch : KeyOutput κ × KeyOutput κ → Prop
  | (some a, some b) => a ≠ b
  | _ => False

instance keyPairMismatchDecidable :
    DecidablePred (keyPairMismatch : KeyOutput κ × KeyOutput κ → Prop) := by
  intro pair
  classical
  exact Classical.propDecidable _

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_abort_left (out : KeyOutput κ) :
    ¬ keyPairMismatch ((KeyOutput.abort : KeyOutput κ), out) := by
  cases out <;> simp [keyPairMismatch, KeyOutput.abort]

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_abort_right (out : KeyOutput κ) :
    ¬ keyPairMismatch (out, (KeyOutput.abort : KeyOutput κ)) := by
  cases out <;> simp [keyPairMismatch, KeyOutput.abort]

omit [Fintype κ] [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem keyPairMismatch_key_key (a b : κ) :
    keyPairMismatch (KeyOutput.key a, KeyOutput.key b) ↔ a ≠ b := by
  simp [keyPairMismatch, KeyOutput.key]

/-- Probability of the explicit-abort correctness-bad event: neither side
aborts and the retained keys differ.  This event is already source-aligned for
Renner correctness. -/
def keyPairMismatchProbability
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : ℝ :=
  by
    classical
    exact
      ∑ pair : KeyOutput κ × KeyOutput κ,
        if keyPairMismatch pair then (ρ.marginalA.matrix pair pair).re else 0

omit [Nonempty κ] in
@[simp]
theorem keyPairMismatchProbability_eq_sum
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    keyPairMismatchProbability ρ =
      ∑ pair : KeyOutput κ × KeyOutput κ,
        if keyPairMismatch pair then (ρ.marginalA.matrix pair pair).re else 0 :=
  by
    classical
    rfl

/-- Conditioned/no-abort helper: trace out Bob's key output while retaining
Alice's explicit key output and the side-information register.  Source-facing
secrecy uses `successfulAliceKeySideInfoState` instead. -/
def conditionedAliceKeySideInfoState
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    State (KeyOutput κ × e) where
  matrix := fun ae ae' =>
    ∑ bob : KeyOutput κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2)
  pos := by
    let block : KeyOutput κ → CMatrix (KeyOutput κ × e) := fun bob =>
      ρ.matrix.submatrix
        (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
        (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
    have hsum : (∑ bob : KeyOutput κ, block bob).PosSemidef := by
      classical
      refine Matrix.posSemidef_sum Finset.univ fun bob _ => ?_
      exact ρ.pos.submatrix (fun ae : KeyOutput κ × e => ((ae.1, bob), ae.2))
    convert hsum using 1
    ext ae ae'
    simp [block, Matrix.sum_apply]
  trace_eq_one := by
    rw [← ρ.trace_eq_one]
    rw [Matrix.trace]
    change
      (∑ ae : KeyOutput κ × e, ∑ bob : KeyOutput κ,
        ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
      ∑ x : (KeyOutput κ × KeyOutput κ) × e, ρ.matrix x x
    calc
      (∑ ae : KeyOutput κ × e, ∑ bob : KeyOutput κ,
          ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
          ∑ alice : KeyOutput κ, ∑ side : e, ∑ bob : KeyOutput κ,
            ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
        rw [Fintype.sum_prod_type]
      _ =
          ∑ alice : KeyOutput κ, ∑ bob : KeyOutput κ, ∑ side : e,
            ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
        apply Finset.sum_congr rfl
        intro alice _
        rw [Finset.sum_comm]
      _ = ∑ x : (KeyOutput κ × KeyOutput κ) × e, ρ.matrix x x := by
        simp [Fintype.sum_prod_type]

omit [Nonempty κ] in
@[simp]
theorem aliceKeySideInfoState_matrix
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    (conditionedAliceKeySideInfoState ρ).matrix =
      fun ae ae' =>
        ∑ bob : KeyOutput κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2) :=
  rfl

/-- Extract the successful key-pair/side-information branch from an
explicit-abort normalized output state.  Only outcomes where Alice and Bob both
retain keys survive; the trace of the result is the success probability. -/
def successfulKeyPairSideInfoState
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    SubnormalizedState ((κ × κ) × e) where
  matrix := fun x y =>
    ρ.matrix
      ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)
      ((KeyOutput.key y.1.1, KeyOutput.key y.1.2), y.2)
  pos := ρ.pos.submatrix
    fun x : (κ × κ) × e => ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)
  trace_le_one := by
    classical
    let f : (κ × κ) × e → (KeyOutput κ × KeyOutput κ) × e :=
      fun x => ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)
    let g : (KeyOutput κ × KeyOutput κ) × e → ℝ := fun y => (ρ.matrix y y).re
    have hf : Function.Injective f := by
      intro x y hxy
      cases x
      cases y
      simp [f, KeyOutput.key] at hxy ⊢
      rcases hxy with ⟨⟨hAlice, hBob⟩, hSide⟩
      exact ⟨Prod.ext hAlice hBob, hSide⟩
    have hsuccess_eq_image :
        (∑ x : (κ × κ) × e, g (f x)) = (Finset.univ.image f).sum g := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact hf hxy
    have himage_le_univ :
        (Finset.univ.image f).sum g ≤ ∑ y : (KeyOutput κ × KeyOutput κ) × e, g y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro y _; exact Finset.mem_univ y)
        (by
          intro y _ _hy
          exact (Complex.nonneg_iff.mp (ρ.pos.diag_nonneg (i := y))).1)
    calc
      (∑ x : (κ × κ) × e,
          ρ.matrix
            ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)
            ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)).re =
          ∑ x : (κ × κ) × e, g (f x) := by
        simp [f, g]
      _ ≤ ∑ y : (KeyOutput κ × KeyOutput κ) × e, g y := by
        rw [hsuccess_eq_image]
        exact himage_le_univ
      _ = (∑ y : (KeyOutput κ × KeyOutput κ) × e, ρ.matrix y y).re := by
        simp [g]
      _ = ρ.matrix.trace.re := by
        rfl
      _ = 1 := by
        rw [ρ.trace_eq_one]
        norm_num

omit [Nonempty κ] in
@[simp]
theorem successfulKeyPairSideInfoState_matrix
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    (successfulKeyPairSideInfoState ρ).matrix =
      fun x y =>
        ρ.matrix
          ((KeyOutput.key x.1.1, KeyOutput.key x.1.2), x.2)
          ((KeyOutput.key y.1.1, KeyOutput.key y.1.2), y.2) :=
  rfl

/-- Trace out Bob's retained key from the successful key-pair branch, keeping
Alice's key and side information as a subnormalized successful branch. -/
def successfulAliceKeySideInfoState
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    SubnormalizedState (κ × e) where
  matrix := fun ae ae' =>
    ∑ bob : κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2)
  pos := by
    let block : κ → CMatrix (κ × e) := fun bob =>
      ρ.matrix.submatrix
        (fun ae : κ × e => ((ae.1, bob), ae.2))
        (fun ae : κ × e => ((ae.1, bob), ae.2))
    have hsum : (∑ bob : κ, block bob).PosSemidef := by
      classical
      refine Matrix.posSemidef_sum Finset.univ fun bob _ => ?_
      exact ρ.pos.submatrix (fun ae : κ × e => ((ae.1, bob), ae.2))
    convert hsum using 1
    ext ae ae'
    simp [block, Matrix.sum_apply]
  trace_le_one := by
    have htrace :
        (∑ ae : κ × e, ∑ bob : κ,
          ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
          ρ.matrix.trace := by
      rw [Matrix.trace]
      calc
        (∑ ae : κ × e, ∑ bob : κ,
            ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)) =
            ∑ alice : κ, ∑ side : e, ∑ bob : κ,
              ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
          rw [Fintype.sum_prod_type]
        _ =
            ∑ alice : κ, ∑ bob : κ, ∑ side : e,
              ρ.matrix ((alice, bob), side) ((alice, bob), side) := by
          apply Finset.sum_congr rfl
          intro alice _
          rw [Finset.sum_comm]
        _ = ∑ x : (κ × κ) × e, ρ.matrix x x := by
          simp [Fintype.sum_prod_type]
    change (∑ ae : κ × e, ∑ bob : κ,
      ρ.matrix ((ae.1, bob), ae.2) ((ae.1, bob), ae.2)).re ≤ 1
    rw [htrace]
    exact ρ.trace_le_one

omit [Nonempty κ] in
@[simp]
theorem successfulAliceKeySideInfoState_matrix
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    (successfulAliceKeySideInfoState ρ).matrix =
      fun ae ae' =>
        ∑ bob : κ, ρ.matrix ((ae.1, bob), ae.2) ((ae'.1, bob), ae'.2) :=
  rfl

/-- Same-key pair distribution on the retained key space, with no abort
coordinate. -/
def uniformRetainedSameKeyPairProb : κ × κ → ℝ≥0
  | (a, b) => if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0

omit [Nonempty κ] in
@[simp]
theorem uniformRetainedSameKeyPairProb_key_key (a b : κ) :
    uniformRetainedSameKeyPairProb (κ := κ) (a, b) =
      if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0 := by
  simp [uniformRetainedSameKeyPairProb]

theorem uniformRetainedSameKeyPairProb_sum :
    (∑ pair : κ × κ, uniformRetainedSameKeyPairProb (κ := κ) pair) = 1 := by
  rw [Fintype.sum_prod_type]
  simp [uniformRetainedSameKeyPairProb]

/-- Source-facing retained same-key pair state `ρ_UU`, with no abort
coordinate. -/
def uniformRetainedSameKeyPairState : State (κ × κ) :=
  Classical.diagonalState (uniformRetainedSameKeyPairProb (κ := κ))
    uniformRetainedSameKeyPairProb_sum

@[simp]
theorem uniformRetainedSameKeyPairState_matrix :
    (uniformRetainedSameKeyPairState (κ := κ)).matrix =
      Matrix.diagonal fun pair => (uniformRetainedSameKeyPairProb (κ := κ) pair : ℂ) :=
  rfl

/-- Source-facing Renner ideal key-pair state for a successful pair branch:
same uniform key pair, independent side information, and the same trace/mass as
the real successful branch. -/
def rennerIdealKeyPairStateFor
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    SubnormalizedState ((κ × κ) × e) :=
  (uniformRetainedSameKeyPairState (κ := κ)).toSubnormalized.prod ρ.marginalB

@[simp]
theorem rennerIdealKeyPairStateFor_matrix
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    (rennerIdealKeyPairStateFor ρ).matrix =
      Matrix.kronecker (uniformRetainedSameKeyPairState (κ := κ)).matrix
        ρ.marginalB.matrix :=
  rfl

/-- Probability of the Renner correctness-bad event on the successful
key-pair branch: Alice and Bob both produced keys, but the retained values
differ. -/
def rennerKeyPairMismatchProbability
    (ρ : SubnormalizedState ((κ × κ) × e)) : ℝ :=
  by
    classical
    exact
      ∑ pair : κ × κ,
        if pair.1 ≠ pair.2 then (ρ.marginalA.matrix pair pair).re else 0

omit [Nonempty κ] in
@[simp]
theorem rennerKeyPairMismatchProbability_eq_sum
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    rennerKeyPairMismatchProbability ρ =
      ∑ pair : κ × κ,
        if pair.1 ≠ pair.2 then (ρ.marginalA.matrix pair pair).re else 0 :=
  by
    classical
    rfl

/-- Renner key-pair security distance on the subnormalized successful
branch. -/
def rennerKeyPairSecurityDistance
    (ρ : SubnormalizedState ((κ × κ) × e)) : ℝ :=
  QIT.normalizedTraceDistance ρ.matrix (rennerIdealKeyPairStateFor ρ).matrix

/-- Source-facing Renner real-vs-ideal key-pair security predicate. -/
def IsRennerEpsilonSecureKeyPair (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) : Prop :=
  rennerKeyPairSecurityDistance ρ ≤ ε

/-- Source-facing Renner correctness of key distillation on the successful
branch. -/
def IsRennerEpsilonCorrectKey (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) : Prop :=
  rennerKeyPairMismatchProbability ρ ≤ ε

/-- Source-facing Renner secrecy of Alice's retained key against side
information. -/
def IsRennerEpsilonSecretAliceKey (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) : Prop :=
  IsRennerEpsilonSecretKey ε (successfulAliceKeySideInfoState ρ)

/-- Renner's correctness/secrecy split on the successful branch. -/
def IsRennerEpsilonCorrectAndSecret (εcorr εsec : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) : Prop :=
  IsRennerEpsilonCorrectKey εcorr ρ ∧ IsRennerEpsilonSecretAliceKey εsec ρ

/-- Source-facing full-security scaffold: correctness and secrecy are available
with errors whose sum is bounded by `ε`.  This remains a definition-level
scaffold, not the heavier trace-distance implication theorem. -/
def IsRennerEpsilonFullSecurityScaffold (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) : Prop :=
  ∃ εcorr εsec : ℝ,
    εcorr + εsec ≤ ε ∧ IsRennerEpsilonCorrectAndSecret εcorr εsec ρ

omit [Nonempty κ] in
@[simp]
theorem isRennerEpsilonCorrectKey_iff (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    IsRennerEpsilonCorrectKey ε ρ ↔ rennerKeyPairMismatchProbability ρ ≤ ε :=
  Iff.rfl

@[simp]
theorem isRennerEpsilonSecretAliceKey_iff (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    IsRennerEpsilonSecretAliceKey ε ρ ↔
      IsRennerEpsilonSecretKey ε (successfulAliceKeySideInfoState ρ) :=
  Iff.rfl

@[simp]
theorem isRennerEpsilonSecureKeyPair_iff (ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    IsRennerEpsilonSecureKeyPair ε ρ ↔ rennerKeyPairSecurityDistance ρ ≤ ε :=
  Iff.rfl

@[simp]
theorem rennerKeyPairSecurityDistance_eq_normalizedTraceDistance
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    rennerKeyPairSecurityDistance ρ =
      QIT.normalizedTraceDistance ρ.matrix (rennerIdealKeyPairStateFor ρ).matrix :=
  rfl

theorem renner_correct_and_secret_of_bounds {εcorr εsec ε : ℝ}
    {ρ : SubnormalizedState ((κ × κ) × e)}
    (hsum : εcorr + εsec ≤ ε)
    (hcorr : IsRennerEpsilonCorrectKey εcorr ρ)
    (hsec : IsRennerEpsilonSecretAliceKey εsec ρ) :
    IsRennerEpsilonFullSecurityScaffold ε ρ :=
  ⟨εcorr, εsec, hsum, ⟨hcorr, hsec⟩⟩

/-! ## Conditioned/no-abort helpers

The following `conditioned...` definitions preserve the older normalized
zero-abort API for callers that have already conditioned on no abort. They are
not the source-facing Renner key-distillation security definitions. -/

/-- Conditioned/no-abort same-key pair distribution: abort has probability zero
and the two retained key outputs are equal and uniform. -/
def conditionedUniformSameKeyPairProb : KeyOutput κ × KeyOutput κ → ℝ≥0
  | (some a, some b) => if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0
  | _ => 0

omit [Nonempty κ] in
@[simp]
theorem conditionedUniformSameKeyPairProb_abort_left (out : KeyOutput κ) :
    conditionedUniformSameKeyPairProb ((KeyOutput.abort : KeyOutput κ), out) = 0 := by
  cases out <;> simp [conditionedUniformSameKeyPairProb, KeyOutput.abort]

omit [Nonempty κ] in
@[simp]
theorem conditionedUniformSameKeyPairProb_abort_right (out : KeyOutput κ) :
    conditionedUniformSameKeyPairProb (out, (KeyOutput.abort : KeyOutput κ)) = 0 := by
  cases out <;> simp [conditionedUniformSameKeyPairProb, KeyOutput.abort]

omit [Nonempty κ] in
@[simp]
theorem conditionedUniformSameKeyPairProb_key_key (a b : κ) :
    conditionedUniformSameKeyPairProb (KeyOutput.key a, KeyOutput.key b) =
      if a = b then (Fintype.card κ : ℝ≥0)⁻¹ else 0 := by
  simp [conditionedUniformSameKeyPairProb, KeyOutput.key]

theorem conditionedUniformSameKeyPairProb_sum :
    (∑ pair : KeyOutput κ × KeyOutput κ,
      conditionedUniformSameKeyPairProb (κ := κ) pair) = 1 := by
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_option]
  simp [conditionedUniformSameKeyPairProb, Fintype.sum_option]

/-- Conditioned/no-abort same-key pair state `ρ_UU`. -/
def conditionedUniformSameKeyPairState : State (KeyOutput κ × KeyOutput κ) :=
  Classical.diagonalState (conditionedUniformSameKeyPairProb (κ := κ))
    conditionedUniformSameKeyPairProb_sum

@[simp]
theorem conditionedUniformSameKeyPairState_matrix :
    (conditionedUniformSameKeyPairState (κ := κ)).matrix =
      Matrix.diagonal fun pair => (conditionedUniformSameKeyPairProb (κ := κ) pair : ℂ) :=
  rfl

/-- Conditioned/no-abort ideal key-pair state associated to a real
key-pair/side-information state. -/
def conditionedIdealKeyPairStateFor
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    State ((KeyOutput κ × KeyOutput κ) × e) :=
  (conditionedUniformSameKeyPairState (κ := κ)).prod ρ.marginalB

@[simp]
theorem conditionedIdealKeyPairStateFor_matrix
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    (conditionedIdealKeyPairStateFor ρ).matrix =
      Matrix.kronecker (conditionedUniformSameKeyPairState (κ := κ)).matrix
        ρ.marginalB.matrix :=
  rfl

/-- Conditioned/no-abort key-pair security distance to the ideal same-key pair
product state. -/
def conditionedKeyPairSecurityDistance
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : ℝ :=
  ρ.normalizedTraceDistance (conditionedIdealKeyPairStateFor ρ)

/-- Conditioned/no-abort real-vs-ideal key-pair security predicate. -/
def IsConditionedEpsilonSecureKeyPair (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) : Prop :=
  conditionedKeyPairSecurityDistance ρ ≤ ε

@[simp]
theorem isConditionedEpsilonSecureKeyPair_iff (ε : ℝ)
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    IsConditionedEpsilonSecureKeyPair ε ρ ↔
      conditionedKeyPairSecurityDistance ρ ≤ ε :=
  Iff.rfl

@[simp]
theorem conditionedKeyPairSecurityDistance_eq_normalizedTraceDistance
    (ρ : State ((KeyOutput κ × KeyOutput κ) × e)) :
    conditionedKeyPairSecurityDistance ρ =
      ρ.normalizedTraceDistance (conditionedIdealKeyPairStateFor ρ) :=
  rfl

namespace KeyDistillation

/-- Public catalog entrypoint for the key-distillation correctness/secrecy
scaffold on Renner's subnormalized successful branch. -/
public theorem main (εcorr εsec ε : ℝ)
    (ρ : SubnormalizedState ((κ × κ) × e)) :
    IsRennerEpsilonCorrectKey εcorr ρ →
      IsRennerEpsilonSecretAliceKey εsec ρ →
        εcorr + εsec ≤ ε →
          IsRennerEpsilonFullSecurityScaffold ε ρ := by
  intro hcorr hsec hsum
  exact renner_correct_and_secret_of_bounds hsum hcorr hsec

end KeyDistillation

end

end QIT.Security
