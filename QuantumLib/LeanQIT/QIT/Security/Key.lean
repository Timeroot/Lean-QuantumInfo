/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Classical.Bridge
public import QIT.States.Subnormalized
public import QIT.States.TraceNorm.Distance
public import Mathlib.Data.Fintype.Option

/-!
# Trace-distance key security predicates

Definition-level API for finite normalized key-security predicates, following
[Renner2005QkdSecurity, main.tex:2488-2514] and
[Renner2005QkdSecurity, main.tex:6704-6718].
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal

namespace QIT.Security

universe u v

noncomputable section

/-- A key output is either an explicit abort or a retained key value. -/
abbrev KeyOutput (κ : Type u) := Option κ

namespace KeyOutput

variable {κ : Type u}

/-- The explicit abort output. -/
def abort : KeyOutput κ :=
  none

/-- A retained key output. -/
def key (k : κ) : KeyOutput κ :=
  some k

@[simp]
theorem abort_eq_none : (abort : KeyOutput κ) = none :=
  rfl

@[simp]
theorem key_eq_some (k : κ) : key k = some k :=
  rfl

@[simp]
theorem abort_ne_key (k : κ) : (abort : KeyOutput κ) ≠ key k := by
  simp [abort, key]

@[simp]
theorem key_ne_abort (k : κ) : key k ≠ (abort : KeyOutput κ) := by
  simp [abort, key]

end KeyOutput

variable {κ : Type u} {e : Type v}
variable [Fintype κ] [DecidableEq κ] [Nonempty κ]
variable [Fintype e] [DecidableEq e]

/-- The uniform distribution on the actual retained key space. -/
def uniformKeyProb (_k : κ) : ℝ≥0 :=
  (Fintype.card κ : ℝ≥0)⁻¹

omit [DecidableEq κ] in
theorem uniformKeyProb_sum :
    (∑ k : κ, uniformKeyProb (κ := κ) k) = 1 := by
  simp [uniformKeyProb]

/-- The ideal uniform state on the actual retained key space, with no abort
coordinate. -/
def uniformKeyState : State κ :=
  Classical.diagonalState (uniformKeyProb (κ := κ)) uniformKeyProb_sum

@[simp]
theorem uniformKeyState_matrix :
    (uniformKeyState (κ := κ)).matrix =
      Matrix.diagonal fun k => (uniformKeyProb (κ := κ) k : ℂ) :=
  rfl

/-- Source-facing Renner ideal state for a successful key branch: the key is
uniform and independent, while the side-information marginal keeps the same
subnormalized trace/mass as the real successful branch. -/
def rennerIdealKeyStateFor (ρ : SubnormalizedState (κ × e)) :
    SubnormalizedState (κ × e) :=
  (uniformKeyState (κ := κ)).toSubnormalized.prod ρ.marginalB

@[simp]
theorem rennerIdealKeyStateFor_matrix (ρ : SubnormalizedState (κ × e)) :
    (rennerIdealKeyStateFor ρ).matrix =
      Matrix.kronecker (uniformKeyState (κ := κ)).matrix ρ.marginalB.matrix :=
  rfl

/-- Renner trace-distance secrecy distance on the subnormalized successful
branch. Abort executions are absent from this branch; its trace is the success
probability. -/
def rennerSecrecyDistance (ρ : SubnormalizedState (κ × e)) : ℝ :=
  QIT.normalizedTraceDistance ρ.matrix (rennerIdealKeyStateFor ρ).matrix

@[simp]
theorem rennerSecrecyDistance_eq_normalizedTraceDistance
    (ρ : SubnormalizedState (κ × e)) :
    rennerSecrecyDistance ρ =
      QIT.normalizedTraceDistance ρ.matrix (rennerIdealKeyStateFor ρ).matrix :=
  rfl

/-- Source-facing Renner `ε`-secret key predicate on the subnormalized
successful branch. -/
def IsRennerEpsilonSecretKey (ε : ℝ) (ρ : SubnormalizedState (κ × e)) : Prop :=
  rennerSecrecyDistance ρ ≤ ε

@[simp]
theorem isRennerEpsilonSecretKey_iff (ε : ℝ) (ρ : SubnormalizedState (κ × e)) :
    IsRennerEpsilonSecretKey ε ρ ↔ rennerSecrecyDistance ρ ≤ ε :=
  Iff.rfl

/-- Extract the successful key/side-information branch from an explicit-abort
normalized output state. The result is subnormalized; its trace is the success
probability. -/
def successfulKeySideInfoState (ρ : State (KeyOutput κ × e)) :
    SubnormalizedState (κ × e) where
  matrix := fun x y => ρ.matrix (KeyOutput.key x.1, x.2) (KeyOutput.key y.1, y.2)
  pos := ρ.pos.submatrix fun x : κ × e => (KeyOutput.key x.1, x.2)
  trace_le_one := by
    classical
    let f : κ × e → KeyOutput κ × e := fun x => (KeyOutput.key x.1, x.2)
    let g : KeyOutput κ × e → ℝ := fun y => (ρ.matrix y y).re
    have hf : Function.Injective f := by
      intro x y hxy
      cases x
      cases y
      simpa [f, KeyOutput.key] using hxy
    have hsuccess_eq_image :
        (∑ x : κ × e, g (f x)) = (Finset.univ.image f).sum g := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact hf hxy
    have himage_le_univ :
        (Finset.univ.image f).sum g ≤ ∑ y : KeyOutput κ × e, g y := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro y _; exact Finset.mem_univ y)
        (by
          intro y _ _hy
          exact (Complex.nonneg_iff.mp (ρ.pos.diag_nonneg (i := y))).1)
    calc
      (∑ x : κ × e,
          ρ.matrix (KeyOutput.key x.1, x.2) (KeyOutput.key x.1, x.2)).re =
          ∑ x : κ × e, g (f x) := by
        simp [f, g]
      _ ≤ ∑ y : KeyOutput κ × e, g y := by
        rw [hsuccess_eq_image]
        exact himage_le_univ
      _ = (∑ y : KeyOutput κ × e, ρ.matrix y y).re := by
        simp [g]
      _ = ρ.matrix.trace.re := by
        rfl
      _ = 1 := by
        rw [ρ.trace_eq_one]
        norm_num

omit [Nonempty κ] in
@[simp]
theorem successfulKeySideInfoState_matrix (ρ : State (KeyOutput κ × e)) :
    (successfulKeySideInfoState ρ).matrix =
      fun x y => ρ.matrix (KeyOutput.key x.1, x.2) (KeyOutput.key y.1, y.2) :=
  rfl

/-! ## Conditioned/no-abort helpers

The following `conditioned...` definitions preserve the older normalized
zero-abort API for callers that have already conditioned on no abort. They are
not the source-facing Renner secrecy definitions. -/

/-- Conditioned/no-abort ideal key-output distribution: abort has weight zero,
keys are uniform. -/
def conditionedUniformKeyOutputProb : KeyOutput κ -> ℝ≥0
  | none => 0
  | some _ => (Fintype.card κ : ℝ≥0)⁻¹

omit [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem conditionedUniformKeyOutputProb_abort :
    conditionedUniformKeyOutputProb (κ := κ) KeyOutput.abort = 0 :=
  rfl

omit [DecidableEq κ] [Nonempty κ] in
@[simp]
theorem conditionedUniformKeyOutputProb_key (k : κ) :
    conditionedUniformKeyOutputProb (κ := κ) (KeyOutput.key k) =
      (Fintype.card κ : ℝ≥0)⁻¹ :=
  rfl

omit [DecidableEq κ] in
theorem conditionedUniformKeyOutputProb_sum :
    (∑ out : KeyOutput κ, conditionedUniformKeyOutputProb (κ := κ) out) = 1 := by
  rw [Fintype.sum_option]
  simp [conditionedUniformKeyOutputProb]

/-- Conditioned/no-abort uniform key-output state with explicit abort
probability zero. -/
def conditionedUniformKeyOutputState : State (KeyOutput κ) :=
  Classical.diagonalState (conditionedUniformKeyOutputProb (κ := κ))
    conditionedUniformKeyOutputProb_sum

@[simp]
theorem conditionedUniformKeyOutputState_matrix :
    (conditionedUniformKeyOutputState (κ := κ)).matrix =
      Matrix.diagonal fun out => (conditionedUniformKeyOutputProb (κ := κ) out : ℂ) :=
  rfl

/-- Conditioned/no-abort product of a uniform key output and adversarial side
information. -/
def conditionedIdealKeySideInfoState (σE : State e) : State (KeyOutput κ × e) :=
  (conditionedUniformKeyOutputState (κ := κ)).prod σE

@[simp]
theorem conditionedIdealKeySideInfoState_matrix (σE : State e) :
    (conditionedIdealKeySideInfoState (κ := κ) σE).matrix =
      Matrix.kronecker (conditionedUniformKeyOutputState (κ := κ)).matrix σE.matrix :=
  rfl

/-- Conditioned/no-abort ideal state associated to a real key-side-information
state. -/
def conditionedIdealKeyStateFor
    (ρ : State (KeyOutput κ × e)) : State (KeyOutput κ × e) :=
  conditionedIdealKeySideInfoState (κ := κ) ρ.marginalB

@[simp]
theorem conditionedIdealKeyStateFor_matrix (ρ : State (KeyOutput κ × e)) :
    (conditionedIdealKeyStateFor ρ).matrix =
      Matrix.kronecker (conditionedUniformKeyOutputState (κ := κ)).matrix
        ρ.marginalB.matrix :=
  rfl

theorem conditionedIdealKeyStateFor_conditionedIdealKeySideInfoState (σE : State e) :
    conditionedIdealKeyStateFor (κ := κ)
        (conditionedIdealKeySideInfoState (κ := κ) σE) =
      conditionedIdealKeySideInfoState (κ := κ) σE := by
  have hm :
      (conditionedIdealKeySideInfoState (κ := κ) σE).marginalB = σE := by
    apply State.ext
    exact State.partialTraceA_prod (conditionedUniformKeyOutputState (κ := κ)) σE
  unfold conditionedIdealKeyStateFor
  rw [hm]

/-- Conditioned/no-abort distance from uniform `d(ρ_AB | B)`, without the
factor `1 / 2`. -/
def conditionedDistanceFromUniformGiven (ρ : State (KeyOutput κ × e)) : ℝ :=
  ρ.traceNormDistance (conditionedIdealKeyStateFor ρ)

@[simp]
theorem conditionedDistanceFromUniformGiven_eq_traceNormDistance
    (ρ : State (KeyOutput κ × e)) :
    conditionedDistanceFromUniformGiven ρ =
      ρ.traceNormDistance (conditionedIdealKeyStateFor ρ) :=
  rfl

/-- Conditioned/no-abort secrecy distance, using the
`1 / 2 * ‖real - ideal‖₁` convention. -/
def conditionedSecrecyDistance (ρ : State (KeyOutput κ × e)) : ℝ :=
  ρ.normalizedTraceDistance (conditionedIdealKeyStateFor ρ)

@[simp]
theorem conditionedSecrecyDistance_eq_normalizedTraceDistance
    (ρ : State (KeyOutput κ × e)) :
    conditionedSecrecyDistance ρ =
      ρ.normalizedTraceDistance (conditionedIdealKeyStateFor ρ) :=
  rfl

/-- A conditioned/no-abort perfect key is exactly the uniform key product with
its side information. -/
def IsConditionedPerfectKey (ρ : State (KeyOutput κ × e)) : Prop :=
  ρ = conditionedIdealKeyStateFor ρ

/-- Conditioned/no-abort `ε`-secret key helper. Source-facing secrecy uses
`IsRennerEpsilonSecretKey` instead. -/
def IsConditionedEpsilonSecretKey (ε : ℝ) (ρ : State (KeyOutput κ × e)) : Prop :=
  conditionedSecrecyDistance ρ ≤ ε

@[simp]
theorem isConditionedPerfectKey_iff (ρ : State (KeyOutput κ × e)) :
    IsConditionedPerfectKey ρ ↔ ρ = conditionedIdealKeyStateFor ρ :=
  Iff.rfl

@[simp]
theorem isConditionedEpsilonSecretKey_iff (ε : ℝ) (ρ : State (KeyOutput κ × e)) :
    IsConditionedEpsilonSecretKey ε ρ ↔ conditionedSecrecyDistance ρ ≤ ε :=
  Iff.rfl

theorem conditionedSecrecyDistance_ideal (ρ : State (KeyOutput κ × e)) :
    conditionedSecrecyDistance (conditionedIdealKeyStateFor ρ) = 0 := by
  rw [show conditionedIdealKeyStateFor ρ =
      conditionedIdealKeySideInfoState (κ := κ) ρ.marginalB from rfl]
  simp [conditionedSecrecyDistance,
    conditionedIdealKeyStateFor_conditionedIdealKeySideInfoState]

theorem isConditionedEpsilonSecretKey_zero_ideal (ρ : State (KeyOutput κ × e)) :
    IsConditionedEpsilonSecretKey 0 (conditionedIdealKeyStateFor ρ) := by
  rw [IsConditionedEpsilonSecretKey, conditionedSecrecyDistance_ideal]

theorem IsConditionedPerfectKey.isConditionedEpsilonSecretKey_zero
    {ρ : State (KeyOutput κ × e)}
    (hρ : IsConditionedPerfectKey ρ) : IsConditionedEpsilonSecretKey 0 ρ := by
  rw [isConditionedPerfectKey_iff] at hρ
  rw [hρ]
  exact isConditionedEpsilonSecretKey_zero_ideal ρ

namespace ComposableKey

/-- Public catalog entrypoint for Renner composable trace-distance key secrecy
on the subnormalized successful branch. -/
public theorem main (ε : ℝ) (ρ : SubnormalizedState (κ × e)) :
    IsRennerEpsilonSecretKey ε ρ ↔ rennerSecrecyDistance ρ ≤ ε :=
  isRennerEpsilonSecretKey_iff ε ρ

end ComposableKey

end

end QIT.Security
