import QuantumInfo.Finite.ResourceTheory.FreeState

open ResourcePretheory
open FreeStateTheory
open NNReal

section hypotesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : ℝ≥0 :=
  ⨅ T ∈ {T : MState d | (Matrix.isHermitian_one.sub T.Hermitian).rinner ρ.Hermitian ≤ ε}, (⨆ σ ∈ S, (T.inner σ) )

end hypotesting

variable {ι : Type*} [FreeStateTheory ι]

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦ OptimalHypothesisRate (ρ⊗^[n]) ε (IsFree (i := i⊗^[n]))) Filter.atTop
    (nhds (RegularizedRelativeEntResource ρ)) := by
  sorry
