/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/
import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.Ensemble
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

open ENNReal
open NNReal
open MState
open Ensemble

/-- Convex roof extension of a function `g : Ket d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice. For example, it is necessary for `le_iInf` and `iInf_le_of_le`.
However, it is also proven in `convex_roof_ne_top` that the convex roof is never `∞`, so the definition `convex_roof` should
be used in most applications. -/
def convex_roof_ENNReal {d : Type _} [Fintype d] [DecidableEq d] (g : Ket d → ℝ≥0) : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : PEnsemble d (Fin n)) (_ : mix (toMEnsemble e) = ρ), ↑(pure_average_NNReal g e)

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble.

This is valued in the extended nonnegative real numbers `ℝ≥0∞` to have good properties of the infimum, which
come from the fact that `ℝ≥0∞` is a complete lattice (see `ENNReal.instCompleteLinearOrder`). However,
it is also proven in `mixed_convex_roof_ne_top` that the mixed convex roof is never `∞`, so the definition `mixed_convex_roof` should
be used in most applications. -/
def mixed_convex_roof_ENNReal {d : Type _} [Fintype d] [DecidableEq d] (f : MState d → ℝ≥0) : MState d → ℝ≥0∞ := fun ρ =>
  ⨅ (n : ℕ+) (e : MEnsemble d (Fin n)) (_ : mix e = ρ), ↑(average_NNReal f e)

variable {d d₁ d₂ : Type _} [Fintype d] [Fintype d₁] [Fintype d₂] [Nonempty d] [Nonempty d₁] [Nonempty d₂]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂]
variable (f : MState d → ℝ≥0)
variable (g : Ket d → ℝ≥0)

/-- The convex roof extension `convex_roof_ENNReal` is never ∞. -/
theorem convex_roof_ne_top : ∀ ρ, convex_roof_ENNReal g ρ ≠ ∞ := fun ρ => by
  simp only [convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall]
  use ⟨Fintype.card d, Fintype.card_pos⟩
  have ed : d ≃ Fin ↑(⟨Fintype.card d, Fintype.card_pos⟩ : ℕ+) := by
    simp only
    exact Fintype.equivFin d
  use (congrPEnsemble ed) <| spectral_ensemble ρ
  rw [mix_congrPEnsemble_eq_mix ed]
  push_neg
  convert spectral_ensemble_mix

omit [Nonempty d] in
/-- The convex roof extension `mixed_convex_roof_ENNReal` is never ∞. -/
theorem mixed_convex_roof_ne_top : ∀ ρ, mixed_convex_roof_ENNReal f ρ ≠ ∞ := fun ρ => by
  simp only [mixed_convex_roof_ENNReal, ne_eq, iInf_eq_top, coe_ne_top, imp_false, not_forall]
  use 1, trivial_mEnsemble ρ 0
  push_neg
  exact trivial_mEnsemble_mix ρ 0

/-- Convex roof extension of a function `g : Ket d → ℝ≥0`, defined as the infimum of all pure-state
ensembles of a given `ρ` of the average of `g` in that ensemble.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `convex_roof_ne_top`. -/
def convex_roof : MState d → ℝ≥0 := fun x ↦ (convex_roof_ENNReal g x).untop (convex_roof_ne_top g x)

/-- Mixed convex roof extension of a function `f : MState d → ℝ≥0`, defined as the infimum of all mixed-state
ensembles of a given `ρ` of the average of `f` on that ensemble.

This is valued in the nonnegative real numbers `ℝ≥0` by applying `ENNReal.toNNReal` to `mixed_convex_roof_ENNReal`. Hence,
it should be used in proofs alongside `mixed_convex_roof_ne_top`. -/
def mixed_convex_roof : MState d → ℝ≥0 := fun x ↦ (mixed_convex_roof_ENNReal f x).untop (mixed_convex_roof_ne_top f x)

/-- Auxiliary function. Convex roof of a function `f : MState d → ℝ≥0` defined over mixed states by resctricting `f` to pure states -/
def convex_roof_of_MState_fun : MState d → ℝ≥0 := convex_roof (f ∘ pure)

-- TODO: make `le_convex_roof`, `convex_roof_le`, `le_mixed_convex_roof` and `mixed_convex_roof_le` if-and-only-if statements.

omit [Nonempty d] in
theorem le_mixed_convex_roof (ρ : MState d) :
  (∀ n > 0, ∀ e : MEnsemble d (Fin n), mix e = ρ → c ≤ average_NNReal f e) → (c ≤ mixed_convex_roof f ρ) := fun h => by
  unfold mixed_convex_roof
  rw [WithTop.le_untop_iff]
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h n hnpos e hmix

theorem le_convex_roof (ρ : MState d) :
  (∀ n > 0, ∀ e : PEnsemble d (Fin n), mix (toMEnsemble e) = ρ → c ≤ pure_average_NNReal g e) → (c ≤ convex_roof g ρ) := fun h => by
  unfold convex_roof
  rw [WithTop.le_untop_iff]
  apply le_iInf; intro ⟨n, hnpos⟩; apply le_iInf; intro e; apply le_iInf; intro hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h n hnpos e hmix

theorem convex_roof_le (ρ : MState d):
(∃ n > 0, ∃ e : PEnsemble d (Fin n), mix (toMEnsemble e) = ρ ∧ pure_average_NNReal g e ≤ c) → (convex_roof g ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold convex_roof
  rw [WithTop.untop_le_iff]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h

omit [Nonempty d] in
theorem mixed_convex_roof_le (ρ : MState d):
(∃ n > 0, ∃ e : MEnsemble d (Fin n), mix e = ρ ∧ average_NNReal f e ≤ c) → (mixed_convex_roof f ρ ≤ c) := fun h => by
  obtain ⟨n, hnpos, e, hmix, h⟩ := h
  unfold mixed_convex_roof
  rw [WithTop.untop_le_iff]
  apply iInf_le_of_le ⟨n, hnpos⟩; apply iInf_le_of_le e; apply iInf_le_of_le hmix
  rw [some_eq_coe', ENNReal.coe_le_coe]
  exact h

/-- The mixed convex roof extension of `f` is smaller than or equal to its convex roof extension, since
the former minimizes over a larger set of ensembles. -/
theorem mixed_convex_roof_le_convex_roof : mixed_convex_roof f ≤ convex_roof_of_MState_fun f := by
  intro ρ
  apply le_convex_roof (f ∘ pure) ρ
  intro n hnpos e hmix
  apply mixed_convex_roof_le
  use n
  apply And.intro hnpos
  use ↑e
  apply And.intro hmix
  exact le_of_eq <| NNReal.coe_inj.mp <| average_of_pure_ensemble (toReal ∘ f) e

/-- The convex roof extension of `g : Ket d → ℝ≥0` applied to a pure state `ψ` is `g ψ`. -/
theorem convex_roof_of_pure (ψ : Ket d) : convex_roof g (pure ψ) = g ψ := by
  rw [le_antisymm_iff]
  constructor
  · apply convex_roof_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_pEnsemble ψ 0
    constructor
    · exact trivial_pEnsemble_mix ψ 0
    · simp only [pure_average_NNReal, Fin.isValue, ← NNReal.coe_le_coe, coe_mk]
      rw [trivial_pEnsemble_average ψ _ 0]
      rfl
  · apply le_convex_roof
    intro n hnpos e hmix
    replace hpure := mix_pEnsemble_pure_iff_pure.mp hmix
    apply le_of_eq
    simp only [pure_average_NNReal, ← NNReal.coe_inj, coe_mk]
    rw [mix_pEnsemble_pure_average (toReal ∘ g) hmix, Function.comp_apply]

omit [Nonempty d] in
/-- The mixed convex roof extension of `f : MState d → ℝ≥0` applied to a pure state `ψ` is `f (pure ψ)`. -/
theorem mixed_convex_roof_of_pure (ψ : Ket d) : mixed_convex_roof f (pure ψ) = f (pure ψ) := by
  rw [le_antisymm_iff]
  constructor
  · apply mixed_convex_roof_le
    use 1; simp only [gt_iff_lt, zero_lt_one, true_and]; use trivial_mEnsemble (pure ψ) 0
    constructor
    · exact trivial_mEnsemble_mix (pure ψ) 0
    · simp only [average_NNReal, Fin.isValue, ← NNReal.coe_le_coe, coe_mk]
      rw [trivial_mEnsemble_average _ (pure ψ) 0]
      rfl
  · apply le_mixed_convex_roof
    intro n hnpos e hmix
    replace hpure := mix_mEnsemble_pure_iff_pure.mp hmix
    apply le_of_eq
    simp only [average_NNReal, ← NNReal.coe_inj, coe_mk]
    rw [mix_mEnsemble_pure_average (toReal ∘ f) hmix, Function.comp_apply]

/-- Entanglement of Formation of bipartite systems. It is the convex roof extension of the
von Neumann entropy of one of the subsystems (here chosen to be the left one, but see `Entropy.Sᵥₙ_of_partial_eq`). -/
def EoF : MState (d₁ × d₂) → ℝ≥0 := convex_roof (fun ψ ↦ ⟨Sᵥₙ (pure ψ).traceRight, Sᵥₙ_nonneg (pure ψ).traceRight⟩)

/-
The partial trace of the maximally entangled state is the maximally mixed state.
-/
theorem traceRight_pure_MES (d : Type*) [Fintype d] [DecidableEq d] [Nonempty d] :
    (MState.pure (Ket.MES d)).traceRight = MState.uniform := by
  -- By definition of partial trace, we sum over the second system.
  have h_partial_trace : ∀ (i j : d), ∑ k : d, (Ket.MES d).vec (i, k) * (star (Ket.MES d).vec (j, k)) = (1 / Fintype.card d : ℝ) * (if i = j then 1 else 0) := by
    unfold Ket.MES
    intro i j
    simp only [one_div, Pi.star_apply, RCLike.star_def, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Complex.ofReal_inv]
    split
    · subst i
      simp only [map_inv₀, Complex.conj_ofReal]
      ring_nf; norm_cast; norm_num;
    · grind [map_zero]
  unfold MState.pure MState.traceRight MState.uniform
  ext i j
  convert h_partial_trace i j
  simp_all only [Pi.star_apply, RCLike.star_def, one_div, Complex.ofReal_inv,
    Complex.ofReal_natCast, mul_ite, mul_one, mul_zero, HermitianMat.toMat_apply,
    coe_ofClassical, Distribution.uniform_def, Finset.card_univ]
  unfold HermitianMat.diagonal
  simp_all only [Complex.ofReal_inv, Complex.ofReal_natCast]
  rfl

/-
The von Neumann entropy of a state is equal to the trace of `ρ log ρ` (technically `cfc ρ negMulLog`).
-/
theorem Sᵥₙ_eq_trace_cfc {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    Sᵥₙ ρ = (HermitianMat.cfc ρ.M Real.negMulLog).trace := by
  -- By definition of von Neumann entropy, we have Sᵥₙ ρ = Finset.sum Finset.univ (fun x ↦ Real.negMulLog (ρ.M.H.eigenvalues x)).
  have h_def : Sᵥₙ ρ = Finset.sum Finset.univ (fun x ↦ Real.negMulLog (ρ.M.H.eigenvalues x)) := by
    rfl
  -- By definition of trace, the trace of `cfc ρ.M Real.negMulLog` is the sum of its eigenvalues.
  have h_trace : (ρ.M.cfc Real.negMulLog).trace =
      ∑ x, (ρ.M.cfc Real.negMulLog).H.eigenvalues x := by
    exact (HermitianMat.sum_eigenvalues_eq_trace _).symm
  obtain ⟨e, he⟩ : ∃ e : d ≃ d, (ρ.M.cfc Real.negMulLog).H.eigenvalues =
      Real.negMulLog ∘ ρ.M.H.eigenvalues ∘ e := by
   exact Matrix.IsHermitian.cfc_eigenvalues _ _
  rw [h_def, h_trace, he]
  simp only [Function.comp_apply]
  conv_lhs => rw [ ← Equiv.sum_comp e ]

/-
The von Neumann entropy of a classical state (diagonal in the basis) is equal to the Shannon entropy of the corresponding distribution.
-/
theorem Sᵥₙ_ofClassical {d : Type*} [Fintype d] [DecidableEq d] (dist : Distribution d) :
    Sᵥₙ (MState.ofClassical dist) = Hₛ dist := by
  -- Let's unfold the definition of `Sᵥₙ` using `Sᵥₙ_eq_trace_cfc`.
  have h_def : Sᵥₙ (MState.ofClassical dist) = (HermitianMat.cfc (MState.ofClassical dist).M Real.negMulLog).trace := by
    exact Sᵥₙ_eq_trace_cfc (ofClassical dist);
  convert h_def using 1;
  -- By definition of $MState.ofClassical$, we know that $(MState.ofClassical dist).M$ is a diagonal matrix with entries $dist i$.
  have h_diag : (MState.ofClassical dist).M = HermitianMat.diagonal (fun x => dist x) := by
    exact rfl;
  rw [ h_diag, HermitianMat.cfc_diagonal, HermitianMat.trace_diagonal ] ; aesop

/-- The entanglement of formation of the maximally entangled state with on-site dimension 𝕕 is log(𝕕). -/
theorem EoF_of_MES : EoF (pure <| Ket.MES d) = Real.log (Finset.card Finset.univ (α := d)) := by
  simp only [EoF, convex_roof_of_pure, coe_mk, Finset.card_univ]
  simp only [traceRight, Matrix.traceRight, MState.pure, Ket.MES, one_div]
  -- The von Neumann entropy of the maximally mixed state is log(d).
  have h_von_neumann : Sᵥₙ (MState.uniform : MState d) = Real.log (Fintype.card d) := by
    rw [MState.uniform, Sᵥₙ_ofClassical Distribution.uniform, Hₛ_uniform, Finset.card_univ]
  convert h_von_neumann using 2;
  convert traceRight_pure_MES d using 1;
  unfold Ket.MES;
  simp_all only [one_div]
  rfl
