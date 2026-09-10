/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QuantumLib.QIT.States.TraceNorm.Distance

/-!
# Quantum fidelity

Root fidelity in the closed form F(ρ,σ) = ‖√ρ √σ‖₁, using the local
`MState.sqrtMatrix` and the trace norm from `QIT.States.TraceNorm.Distance`. This module
also records the squared-fidelity convention F(ρ,σ)^2 used by the
Wilde/Tomamichel Uhlmann route. The squared API is only a convention layer; it
does not prove Uhlmann's theorem, Fuchs-van de Graaf, monotonicity, symmetry, or
spectral trace-norm facts.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder

open QIT

namespace MState

universe u

noncomputable section

variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Quantum fidelity F(ρ,σ) = ‖√ρ √σ‖₁ (trace norm of the sqrt product). -/
def fidelity (ρ σ : MState a) : ℝ :=
  traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix)

/-- Fidelity unfolds to the trace norm of the product of state square roots. -/
@[simp]
theorem fidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix (ρ σ : MState a) :
    ρ.fidelity σ = traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix) :=
  rfl

/-- Fidelity is nonnegative at the current trace-norm/root-fidelity layer. -/
theorem fidelity_nonneg (ρ σ : MState a) : 0 ≤ ρ.fidelity σ :=
  traceNorm_nonneg (ρ.sqrtMatrix * σ.sqrtMatrix)

/-- Squared quantum fidelity, following the Uhlmann-route convention
`F(ρ,σ)^2 = ‖√ρ √σ‖₁^2`.

This is only the local squared-fidelity API needed by the Uhlmann route; it is not
Uhlmann's theorem or a proof of any maximization characterization.
-/
def squaredFidelity (ρ σ : MState a) : ℝ :=
  (ρ.fidelity σ) ^ 2

/-- Squared fidelity unfolds to the square of root fidelity. -/
@[simp]
theorem squaredFidelity_eq_fidelity_sq (ρ σ : MState a) :
    ρ.squaredFidelity σ = (ρ.fidelity σ) ^ 2 :=
  rfl

/-- Squared fidelity unfolds to the squared trace norm of the sqrt product. -/
theorem squaredFidelity_eq_traceNorm_sqrtMatrix_mul_sqrtMatrix_sq (ρ σ : MState a) :
    ρ.squaredFidelity σ = (traceNorm (ρ.sqrtMatrix * σ.sqrtMatrix)) ^ 2 :=
  rfl

/-- Squared fidelity is nonnegative at the current convention layer. -/
theorem squaredFidelity_nonneg (ρ σ : MState a) : 0 ≤ ρ.squaredFidelity σ :=
  sq_nonneg (ρ.fidelity σ)

/-- Self-fidelity reduces definitionally to the trace norm of the density matrix.

The stronger statement `ρ.fidelity ρ = 1` is not claimed here; it requires
trace-norm spectral facts outside the current fidelity layer.
-/
theorem fidelity_self_eq_traceNorm_matrix (ρ : MState a) :
    ρ.fidelity ρ = traceNorm ρ.m := by
  simp [MState.fidelity]

/-- Squared self-fidelity reduces to the squared trace norm of the density matrix.

The stronger statement `ρ.squaredFidelity ρ = 1` is not claimed here; it also
requires trace-norm spectral facts outside the current squared-fidelity layer.
-/
theorem squaredFidelity_self_eq_traceNorm_matrix_sq (ρ : MState a) :
    ρ.squaredFidelity ρ = (traceNorm ρ.m) ^ 2 := by
  simp [MState.squaredFidelity]

end

end MState
