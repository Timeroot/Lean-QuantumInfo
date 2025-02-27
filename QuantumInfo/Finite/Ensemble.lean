import QuantumInfo.Finite.MState

open MState
open Classical
open BigOperators

noncomputable section

/-- A mixed-state ensemble is a random variable valued in `MState d`. That is,
a collection of mixed states `var : α → MState d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev MEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := Distribution.RandVar α (MState d)

/-- A pure-state ensemble is a random variable valued in `Ket d`. That is,
a collection of pure states `var : α → Ket d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev PEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := Distribution.RandVar α (Ket d)

variable {α β d: Type*} [Fintype α] [Fintype β] [Fintype d]

/-- Alias for `Distribution.var` for mixed-state ensembles. -/
abbrev MEnsemble.states [Fintype α] : MEnsemble d α → (α → MState d) := Distribution.RandVar.var

/-- Alias for `Distribution.var` for pure-state ensembles. -/
abbrev PEnsemble.states [Fintype α] : PEnsemble d α → (α → Ket d) := Distribution.RandVar.var

namespace Ensemble

/-- A pure-state ensemble is a mixed-state ensemble if all kets are interpreted as mixed states. -/
@[coe] def toMEnsemble : PEnsemble d α → MEnsemble d α := Functor.map pure

instance : Coe (PEnsemble d α) (MEnsemble d α) := ⟨toMEnsemble⟩

@[simp]
theorem toMEnsemble_mk : (toMEnsemble ⟨ps, distr⟩ : MEnsemble d α) = ⟨pure ∘ ps, distr⟩ :=
  rfl

/-- A mixed-state ensemble comes from a pure-state ensemble if and only if all states are pure. -/
theorem coe_PEnsemble_iff_pure_states (me : MEnsemble d α): (∃ pe : PEnsemble d α, ↑pe = me) ↔ (∃ ψ : α → Ket d, me.states = MState.pure ∘ ψ) := by
  constructor
  · intro ⟨pe, hpe⟩
    use pe.states
    ext1 i
    subst hpe
    rfl
  · intro ⟨ψ, hψ⟩
    use ⟨ψ, me.distr⟩
    simp only [toMEnsemble_mk]
    congr
    exact hψ.symm

/-- The resulting mixed state after mixing the states in an ensemble with their
respective probability weights. Note that, generically, a single mixed state has infinitely many
ensembles that mixes into it. -/
def mix (e : MEnsemble d α) : MState d := Distribution.expect_val e

@[simp]
theorem mix_of (e : MEnsemble d α) : (mix e).m = ∑ i, Prob.toReal (e.distr i) • (e.states i).m := by
  rfl

/-- Two mixed-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrMEnsemble (σ : α ≃ β) : MEnsemble d α ≃ MEnsemble d β := Distribution.congrRandVar σ

/-- Two pure-state ensembles indexed by `\alpha` and `\beta` are equivalent if `α ≃ β`. -/
def congrPEnsemble (σ : α ≃ β) : PEnsemble d α ≃ PEnsemble d β := Distribution.congrRandVar σ

/-- Equivalence of mixed-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrMEnsemble_eq_mix (σ : α ≃ β) (e : MEnsemble d α) : mix (congrMEnsemble σ e) = mix e :=
  Distribution.expect_val_congr_eq_expect_val σ e

/-- Equivalence of pure-state ensembles leaves the resulting mixed state invariant -/
@[simp]
theorem mix_congrPEnsemble_eq_mix (σ : α ≃ β) (e : PEnsemble d α) : mix (toMEnsemble (congrPEnsemble σ e)) = mix (↑e : MEnsemble d α) := by
  unfold toMEnsemble congrPEnsemble mix
  rw [Distribution.map_congr_eq_congr_map MState.pure σ e]
  exact Distribution.expect_val_congr_eq_expect_val σ (MState.pure <$> e)

/-- The average of a function `f : MState d → T`, where `T` is of `Mixable U T` instance, on a mixed-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (e : MEnsemble d α) : T :=
  Distribution.expect_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : MState d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def average_NNReal {d : Type _} [Fintype d] (f : MState d → NNReal) (e : MEnsemble d α) : NNReal :=
  ⟨average (NNReal.toReal ∘ f) e,
    Distribution.zero_le_expect_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of a function `f : Ket d → T`, where `T` is of `Mixable U T` instance, on a pure-state ensemble `e`
is the expectation value of `f` acting on the states of `e`, with the corresponding probability weights from `e.distr`. -/
def pure_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (e : PEnsemble d α) : T :=
  Distribution.expect_val <| f <$> e

/-- A version of `average` conveniently specialized for functions `f : Ket d → ℝ≥0` returning nonnegative reals.
Notably, the average is also a nonnegative real number. -/
def pure_average_NNReal {d : Type _} [Fintype d] (f : Ket d → NNReal) (e : PEnsemble d α) : NNReal :=
  ⟨pure_average (NNReal.toReal ∘ f) e,
    Distribution.zero_le_expect_val e.distr (NNReal.toReal ∘ f ∘ e.states) (fun n => (f <| e.states n).2)⟩

/-- The average of `f : MState d → T` on a coerced pure-state ensemble `↑e : MEnsemble d α`
is equal to averaging the restricted function over Kets `f ∘ pure : Ket d → T` on `e`. -/
theorem average_of_pure_ensemble {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T]
  (f : MState d → T) (e : PEnsemble d α) :
  average f (toMEnsemble e) = pure_average (f ∘ pure) e := by
  simp only [average, pure_average, toMEnsemble, comp_map]

/-- A pure-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal to `ψ`  -/
theorem mix_pEnsemble_pure_iff_pure {ψ : Ket d} {e : PEnsemble d α} :
  mix (toMEnsemble e) = MState.pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = ψ := by
  sorry

/-- The average of `f : Ket d → T` on an ensemble that mixes to a pure state `ψ` is `f ψ` -/
theorem mix_pEnsemble_pure_average {ψ : Ket d} {e : PEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (hmix : mix (toMEnsemble e) = MState.pure ψ) :
  pure_average f e = f ψ := by
  have hpure := mix_pEnsemble_pure_iff_pure.mp hmix
  simp only [pure_average, Functor.map, Distribution.expect_val]
  apply Mixable.to_U_inj
  rw [PEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply, smul_eq_mul, Mixable.mkT_instUniv]
  have h1 : ∀ i ∈ Finset.univ, (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.toReal_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = ψ := fun i hi hne0 ↦ by
    rw [←Prob.val_zero, ←Prob.toReal, Prob.ne_iff] at hne0
    exact hpure i hne0
  rw [←Finset.sum_smul, ←Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

/-- A mixed-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal to `pure ψ`  -/
theorem mix_mEnsemble_pure_iff_pure {ψ : Ket d} {e : MEnsemble d α} :
  mix e = pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = MState.pure ψ := by
  sorry

/-- The average of `f : MState d → T` on an ensemble that mixes to a pure state `ψ` is `f (pure ψ)` -/
theorem mix_mEnsemble_pure_average {ψ : Ket d} {e : MEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (hmix : mix e = pure ψ) :
  average f e = f (pure ψ) := by
  have hpure := mix_mEnsemble_pure_iff_pure.mp hmix
  simp only [average, Functor.map, Distribution.expect_val]
  apply Mixable.to_U_inj
  rw [MEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply, smul_eq_mul, Mixable.mkT_instUniv]
  have h1 : ∀ i ∈ Finset.univ, (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = pure ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (Prob.toReal (e.distr i)) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.toReal_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = pure ψ := fun i hi hne0 ↦ by
    rw [←Prob.val_zero, ←Prob.toReal, Prob.ne_iff] at hne0
    exact hpure i hne0
  rw [←Finset.sum_smul, ←Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

/-- The trivial mixed-state ensemble of `ρ` consists of copies of `rho`, with the `i`-th one having
probability 1. -/
def trivial_mEnsemble (ρ : MState d) (i : α) : MEnsemble d α := ⟨fun _ ↦ ρ, Distribution.constant i⟩

/-- The trivial mixed-state ensemble of `ρ` mixes to `ρ` -/
theorem trivial_mEnsemble_mix (ρ : MState d) : ∀ i : α, mix (trivial_mEnsemble ρ i) = ρ := fun i ↦by
  apply MState.ext_m
  simp only [trivial_mEnsemble, Distribution.constant, mix_of, DFunLike.coe, apply_ite,
    Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- The average of `f : MState d → T` on a trivial ensemble of `ρ` is `f ρ`-/
theorem trivial_mEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (ρ : MState d):
  ∀ i : α, average f (trivial_mEnsemble ρ i) = f ρ := fun i ↦ by
    simp only [average, Functor.map, Distribution.expect_val, trivial_mEnsemble]
    apply Mixable.to_U_inj
    simp only [Distribution.constant_eq, Function.comp_apply, Mixable.to_U_of_mkT, apply_ite,
      Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]

instance MEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (MEnsemble d α) where
  default := trivial_mEnsemble default default

/-- The trivial pure-state ensemble of `ψ` consists of copies of `ψ`, with the `i`-th one having
probability 1. -/
def trivial_pEnsemble (ψ : Ket d) (i : α) : PEnsemble d α := ⟨fun _ ↦ ψ, Distribution.constant i⟩

/-- The trivial pure-state ensemble of `ψ` mixes to `ψ` -/
theorem trivial_pEnsemble_mix (ψ : Ket d) : ∀ i : α, mix (toMEnsemble (trivial_pEnsemble ψ i)) = MState.pure ψ := fun i ↦ by
  apply MState.ext_m
  simp only [trivial_pEnsemble, Distribution.constant, toMEnsemble_mk, mix_of, DFunLike.coe,
    apply_ite, Prob.toReal_one, Prob.toReal_zero, MEnsemble.states, Function.comp_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The average of `f : Ket d → T` on a trivial ensemble of `ψ` is `f ψ`-/
theorem trivial_pEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) (ψ : Ket d) :
  ∀ i : α, pure_average f (trivial_pEnsemble ψ i) = f ψ := fun i ↦ by
    simp only [pure_average, Functor.map, Distribution.expect_val, trivial_pEnsemble]
    apply Mixable.to_U_inj
    simp only [Distribution.constant_eq, Function.comp_apply, Mixable.to_U_of_mkT, apply_ite,
      Prob.toReal_one, Prob.toReal_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]

instance PEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (PEnsemble d α) where
  default := trivial_pEnsemble default default

/-- The spectral pure-state ensemble of `ρ`. The states are its eigenvectors, and the probabilities, eigenvalues. -/
def spectral_ensemble (ρ : MState d) : PEnsemble d d :=
  { var i :=
    { vec := ρ.Hermitian.eigenvectorBasis i
      normalized' := by
        rw [←one_pow 2, ←ρ.Hermitian.eigenvectorBasis.orthonormal.1 i]
        have hnonneg : 0 ≤ ∑ x : d, Complex.normSq (ρ.Hermitian.eigenvectorBasis i x) := by
          simp_rw [Complex.normSq_eq_norm_sq]
          positivity
        simp only [← Complex.normSq_eq_norm_sq, EuclideanSpace.norm_eq, Real.sq_sqrt hnonneg]
    }
    distr := ρ.spectrum}

/-- The spectral pure-state ensemble of `ρ` mixes to `ρ` -/
theorem spectral_ensemble_mix : mix (↑(spectral_ensemble ρ) : MEnsemble d d) = ρ := by
  ext i j
  sorry

end Ensemble
