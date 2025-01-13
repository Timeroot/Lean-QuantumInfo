import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Entropy
import ClassicalInfo.Entropy

/-!
Entanglement measures. (Mixed) convex roof extensions. Definition of product / separable / entangled states
are in `Braket.lean` and/or `MState.lean`

Important definitions:
 * `convex_roof`: Convex roof extension of `g : Ket d → ℝ≥0`
 * `mixed_convex_roof`: Mixed convex roof extension of `f : MState d → ℝ≥0`
 * `EoF`: Entanglement of Formation

TODO:
 - Other entanglement measures (not necessarily based on convex roof extensions). In roughly increasing order of
   difficulty to implement: (Logarithmic) Negativity, Entanglement of Purification, Squashed Entanglement, Relative
   Entropy of Entanglement, Entanglement Cost, Distillable Entanglement.
   For a compendium on the zoo of entanglement measures, see
   [1] Christandl, Matthias. “The Structure of Bipartite Quantum States - Insights from Group Theory and Cryptography.”
       https://doi.org/10.48550/arXiv.quant-ph/0604183.
 - Define classes of entanglement measures with good properties, including: monotonicity under LOCC (easier: just LO),
   monotonicity on average under LOCC, convexity (if the latter two are present, it is called an entanglement monotone
   by some), vanishing on separable states, normalized on the maximally entangled state, (sub)additivity, regularisible.
   For other properties, see [1] above and:
   [2] Szalay, Szilárd. “Multipartite Entanglement Measures.” (mainly Sec. IV)
       https://doi.org/10.1103/PhysRevA.92.042329.
   [3] Horodecki, Ryszard, Paweł Horodecki, Michał Horodecki, and Karol Horodecki. “Quantum Entanglement.”
       https://doi.org/10.1103/RevModPhys.81.865.
 - Useful properties of convex roof extensions:
   1. If f is monotonically non-increasing under LOCC, so is its convex roof.
   2. If f ψ is zero if and only if ψ is a product state, then its convex roof is faithful: zero if and only if
      the mixed state is separable
   For other properties, see Sec. IV.F of [2] above.
-/

noncomputable section

open Classical
open ENNReal
open NNReal
open MState
open MState.Ensemble

variable {d d₁ d₂ : Type _} [Fintype d] [Fintype d₁] [Fintype d₂]
variable (f : MState d → ℝ≥0)
variable (g : Ket d → ℝ≥0)

/-- Convex roof extension of a function `g : Ket d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble. The term "convex roof" is abbreviated as `co`
in other theorems and definitions, following the shorthand notation in the literature.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice. For example, it is necessary for `le_iInf` and `iInf_le_of_le`.
However, it is also proven in `co_ne_top` that the convex roof is never `∞`, so the definition `convex_roof` should
be used in most applications. -/
def convex_roof_ENNReal : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : PEnsemble d (Fin n)) (_ : mix (toMEnsemble e) = ρ), ↑(pure_average_NNReal g e)

/-- Convex roof extension of a function `g : Ket d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble. The term "convex roof" is abbreviated as `co`
in other theorems and definitions, following the shorthand notation in the literature.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `co_ne_top`. -/
def convex_roof : MState d → ℝ≥0 := ENNReal.toNNReal ∘ convex_roof_ENNReal g

/-- The convex roof extension `convex_roof_ENNReal` is never ∞. -/
theorem co_ne_top [instNE : Nonempty d] : ∀ ρ, convex_roof_ENNReal g ρ ≠ ∞ := fun ρ => by
  simp only [convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall, Decidable.not_not]
  use ⟨Fintype.card d, Fintype.card_pos⟩
  have ed : d ≃ Fin ↑(⟨Fintype.card d, Fintype.card_pos⟩ : ℕ+) := by
    simp only
    exact Fintype.equivFin d
  use (congrPEnsemble ed) <| spectral_ensemble ρ
  rw [mix_congrPEnsemble_eq_mix ed]
  exact spectral_ensemble_mix

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble. The term "mixed convex roof" is abbreviated as `mixed_co`
in other theorems and definitions.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice (see `ENNReal.instCompleteLinearOrder`). However,
it is also proven in `mixed_co_ne_top` that the mixed convex roof is never `∞`, so the definition `mixed_convex_roof` should
be used in most applications. -/
def mixed_convex_roof_ENNReal : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : MEnsemble d (Fin n)) (_ : mix e = ρ), ↑(average_NNReal f e)

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble. The term "mixed convex roof" is abbreviated as `mixed_co`
in other theorems and definitions.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `mixed_convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `mixed_co_ne_top`. -/
def mixed_convex_roof : MState d → ℝ≥0 := ENNReal.toNNReal ∘ mixed_convex_roof_ENNReal f

/-- The convex roof extension `mixed_convex_roof_ENNReal` is never ∞. -/
theorem mixed_co_ne_top [Nonempty d] : ∀ ρ, mixed_convex_roof_ENNReal f ρ ≠ ∞ := fun ρ => by
  simp only [mixed_convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall, Decidable.not_not]
  use 1, trivial_mEnsemble ρ 0
  exact trivial_mEnsemble_mix ρ 0

/-- Auxiliary function. Convex roof of a function `f : MState d → ℝ≥0` defined over mixed states by resctricting `f` to pure states -/
def convex_roof_of_MState_fun : MState d → ℝ≥0 := convex_roof (f ∘ pure)

-- TODO: make `le_co`, `co_le`, `le_mixed_co` and `mixed_co_le` if-and-only-if statements.

theorem le_mixed_co [Nonempty d] (ρ : MState d) :
  (∀ n > 0, ∀ e : MEnsemble d (Fin n), mix e = ρ → c ≤ average_NNReal f e) → (c ≤ mixed_convex_roof f ρ) := fun h => by
  unfold mixed_convex_roof
  rw [Function.comp_apply]
  apply ENNReal.le_toNNReal_of_coe_le _ (mixed_co_ne_top f ρ)
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [ENNReal.coe_le_coe]
  exact h n hnpos e hmix

theorem le_co [Nonempty d] (ρ : MState d) :
  (∀ n > 0, ∀ e : PEnsemble d (Fin n), mix (↑e) = ρ → c ≤ pure_average_NNReal g e) → (c ≤ convex_roof g ρ) := fun h => by
  unfold convex_roof
  rw [Function.comp_apply]
  apply ENNReal.le_toNNReal_of_coe_le _ (co_ne_top g ρ)
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [ENNReal.coe_le_coe]
  exact h n hnpos e hmix

theorem co_le [Nonempty d] (ρ : MState d):
(∃ n > 0, ∃ e : PEnsemble d (Fin n), mix (↑e) = ρ ∧ pure_average_NNReal g e ≤ c) → (convex_roof g ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold convex_roof
  rw [Function.comp_apply, ←ENNReal.toNNReal_coe c, ENNReal.toNNReal_le_toNNReal (co_ne_top g ρ) (ENNReal.coe_ne_top)]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [ENNReal.coe_le_coe]
  exact h

theorem mixed_co_le [Nonempty d] (ρ : MState d):
(∃ n > 0, ∃ e : MEnsemble d (Fin n), mix e = ρ ∧ average_NNReal f e ≤ c) → (mixed_convex_roof f ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold mixed_convex_roof
  rw [Function.comp_apply, ←ENNReal.toNNReal_coe c, ENNReal.toNNReal_le_toNNReal (mixed_co_ne_top f ρ) (ENNReal.coe_ne_top)]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [ENNReal.coe_le_coe]
  exact h

/-- The mixed convex roof extension of `f` is smaller than or equal to its convex roof extension, since
the former minimizes over a larger set of ensembles. -/
theorem mixed_co_le_co [Nonempty d] : mixed_convex_roof f ≤ convex_roof_of_MState_fun f := by
  intro ρ
  apply le_co (f ∘ pure) ρ
  intro n hnpos e hmix
  apply mixed_co_le
  use n
  apply And.intro hnpos
  use ↑e
  apply And.intro hmix
  exact le_of_eq <| NNReal.coe_inj.mp <| average_of_pure_ensemble (toReal ∘ f) e

/-- The convex roof extension of `g : Ket d → ℝ≥0` applied to a pure state `ψ` is `g ψ`. -/
theorem co_of_pure [Nonempty d] (ψ : Ket d) : convex_roof g (pure ψ) = g ψ := by
  rw [le_antisymm_iff]
  constructor
  · apply co_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_pEnsemble ψ 0
    constructor
    · exact trivial_pEnsemble_mix ψ 0
    · simp only [pure_average_NNReal, Fin.isValue, ← NNReal.coe_le_coe, coe_mk]
      rw [trivial_pEnsemble_average _ ψ 0]
      rfl
  · apply le_co
    intro n hnpos e hmix
    replace hpure := mix_pEnsemble_pure_iff_pure.mp hmix
    apply le_of_eq
    simp only [pure_average_NNReal, ← NNReal.coe_inj, coe_mk]
    rw [mix_pEnsemble_pure_average (toReal ∘ g) hmix, Function.comp_apply]

/-- The mixed convex roof extension of `f : MState d → ℝ≥0` applied to a pure state `ψ` is `f (pure ψ)`. -/
theorem mixed_co_of_pure [Nonempty d] (ψ : Ket d) : mixed_convex_roof f (pure ψ) = f (pure ψ) := by
  rw [le_antisymm_iff]
  constructor
  · apply mixed_co_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_mEnsemble (pure ψ) 0
    constructor
    · exact trivial_mEnsemble_mix (pure ψ) 0
    · simp only [average_NNReal, Fin.isValue, ← NNReal.coe_le_coe, coe_mk]
      rw [trivial_mEnsemble_average _ (pure ψ) 0]
      rfl
  · apply le_mixed_co
    intro n hnpos e hmix
    replace hpure := mix_mEnsemble_pure_iff_pure.mp hmix
    apply le_of_eq
    simp only [average_NNReal, ← NNReal.coe_inj, coe_mk]
    rw [mix_mEnsemble_pure_average (toReal ∘ f) hmix, Function.comp_apply]

/-- Entanglement of Formation of bipartite systems. It is the convex roof extension of the
von Neumann entropy of one of the subsystems (here chosen to be the left one, but see `Entropy.Sᵥₙ_of_partial_eq`). -/
def EoF : MState (d₁ × d₂) → ℝ≥0 := convex_roof (fun ψ ↦ ⟨Sᵥₙ (pure ψ).traceRight, Sᵥₙ_nonneg (pure ψ).traceRight⟩)

/-- The entanglement of formation of the maximally entangled state with on-site dimension 𝕕 is log(𝕕). -/
theorem EoF_of_MES [Nonempty d] : EoF (pure <| Ket.MES d) = Real.log (Finset.card Finset.univ (α := d)) := by
  simp only [EoF, co_of_pure, coe_mk, Finset.card_univ]
  sorry
