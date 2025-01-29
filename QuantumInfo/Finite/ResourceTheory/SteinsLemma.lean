import QuantumInfo.Finite.ResourceTheory.FreeState

open ResourcePretheory
open FreeStateTheory
open NNReal

section hypotesting
open ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The optimal hypothesis testing rate, for a tolerance ε: given a state ρ and a set of states S,
the optimum distinguishing rate that allows a probability ε of errors. -/
noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : ℝ) (S : Set (MState d)) : ℝ≥0 :=
  ⨅ T ∈ {T : MState d | (Matrix.isHermitian_one.sub T.Hermitian).rinner ρ.Hermitian ≤ ε}, (⨆ σ ∈ S, (T.inner σ) )

private theorem Lemma6 (m : ℕ) (hm : 0 < m) (ρ σf : MState d) (σm : MState (Fin m → d)) (hσf : σf.m.PosDef) (ε : ℝ)
    (hε : 0 < ε) :
    let σn (n : ℕ) : (MState (Fin n → d)) :=
      let l : ℕ := n / m
      let q : ℕ := n % m
      let σl := σm ⊗^ l
      let σr := σf ⊗^ q
      let eqv : (Fin n → d) ≃ (Fin l → Fin m → d) × (Fin q → d) :=
        Equiv.piCongrLeft (fun _ ↦ d) ((finCongr (Eq.symm (Nat.div_add_mod' n m))).trans (finSumFinEquiv.symm))
          |>.trans <|
           (Equiv.sumArrowEquivProdArrow ..)
          |>.trans <|
           (Equiv.prodCongr (Equiv.piCongrLeft (fun _ ↦ d) finProdFinEquiv).symm (Equiv.refl _))
          |>.trans <|
          (Equiv.prodCongr (Equiv.curry ..) (Equiv.refl _))
      (σl.prod σr).relabel eqv
    Filter.atTop.limsup (fun n ↦ -(OptimalHypothesisRate (ρ ⊗^ n) ε {σn n}) / n : ℕ → ℝ) ≤
    (qRelativeEnt (ρ ⊗^ m) σm) / m
  := by
  sorry

end hypotesting

variable {ι : Type*} [FreeStateTheory ι]

theorem GeneralizedQSteinsLemma {i : ι} (ρ : MState (H i)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1) :
    Filter.Tendsto (fun n ↦ OptimalHypothesisRate (ρ⊗^[n]) ε (IsFree (i := i⊗^[n]))) Filter.atTop
    (nhds (RegularizedRelativeEntResource ρ)) := by
  sorry
