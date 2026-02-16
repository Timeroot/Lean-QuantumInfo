/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] (ρ σ : MState d)

--We put all of the fidelity defs and theorems in the MState namespace so that they have the
--nice . syntax, i.e. `ρ.fidelity σ = 1 ↔ ρ = σ`.
namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  ((σ.M.conj ρ.pos.sqrt) ^ (1/2 : ℝ)).trace

set_option maxHeartbeats 0 in
theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ := by
  -- Apply `HermitianMat.trace_nonneg` to the term inside the square root.
    have h_trace_nonneg : 0 ≤ (σ.M.conj ρ.pos.sqrt) ^ (1 / 2 : ℝ) := by
      apply HermitianMat.rpow_nonneg
      apply HermitianMat.conj_nonneg σ.zero_le _
    -- Apply the fact that the trace of a positive semidefinite matrix is non-negative.
    apply HermitianMat.trace_nonneg; assumption

theorem fidelity_le_one : fidelity ρ σ ≤ 1 :=
  sorry --submultiplicativity of trace and sqrt

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def fidelity_prob : Prob :=
  ⟨fidelity ρ σ, ⟨fidelity_ge_zero ρ σ, fidelity_le_one ρ σ⟩⟩

--PULLOUT, CLEANUP
/-
The square root of the positive semidefinite matrix of a state `ρ` is equal to `ρ` raised to the power of 1/2.
-/
theorem MState.pos_sqrt_eq_rpow {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.pos.sqrt = (ρ.M ^ (1/2 : ℝ)).toMat := by
  symm
  convert ( ρ.pos.isHermitian.cfc_eq _ ) using 1;
  refine' congr_arg₂ _ ( congr_arg₂ _ rfl _ ) rfl;
  ext i;
  norm_num [ ← Real.sqrt_eq_rpow ] ;

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  -- Now use the given definition to simplify the expression.
    have h_simp : ((ρ.M.conj (ρ.pos.sqrt)) ^ (1/2 : ℝ)).trace = ((ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).toMat)) ^ (1/2 : ℝ)).trace := by
      rw [ MState.pos_sqrt_eq_rpow ];
    have h_simp2 : (ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).toMat)) = ρ.M ^ (1 + 2 * (1/2) : ℝ) := by
      convert HermitianMat.conj_rpow _ _ _;
      · norm_num;
      · exact ρ.zero_le;
      · norm_num;
      · norm_num;
    have h_simp3 : ((ρ.M ^ (1 + 2 * (1/2) : ℝ)) ^ (1/2 : ℝ)) = ρ.M ^ (1 : ℝ) := by
      rw [ ← HermitianMat.rpow_mul ]
      norm_num
      exact ρ.zero_le
    unfold MState.fidelity; aesop;

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem fidelity_eq_one_iff_self : fidelity ρ σ = 1 ↔ ρ = σ :=
  ⟨sorry,
  fun h ↦ h ▸ fidelity_self_eq_one ρ
  ⟩

/-- The fidelity is a symmetric quantity. -/
theorem fidelity_symm : fidelity ρ σ = fidelity σ ρ :=
  sorry --break into sqrts

/-- The fidelity cannot decrease under the application of a channel. -/
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (Λ : CPTPMap d d₂) : fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end MState
