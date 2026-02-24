/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Leonardo A Lessa
-/
import QuantumInfo.Finite.MState

open MState
open BigOperators

noncomputable section

/-- A mixed-state ensemble is a random variable valued in `MState d`. That is,
a collection of mixed states `var : α → MState d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev MEnsemble (d : Type*) (α : Type*) [Fintype d] [DecidableEq d] [Fintype α] := Distribution.RandVar α (MState d)

/-- A pure-state ensemble is a random variable valued in `Ket d`. That is,
a collection of pure states `var : α → Ket d`, each with their own probability weight
described by `distr : Distribution α`. -/
abbrev PEnsemble (d : Type*) (α : Type*) [Fintype d] [Fintype α] := Distribution.RandVar α (Ket d)

variable {α β d : Type*} [Fintype α] [Fintype β] [Fintype d] [DecidableEq d]

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
theorem mix_of (e : MEnsemble d α) : (mix e).m = ∑ i, (e.distr i : ℝ) • (e.states i).m := by
  apply AddSubgroup.val_finset_sum -- *laughs in defeq*

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
def average_NNReal {d : Type _} [Fintype d] [DecidableEq d] (f : MState d → NNReal) (e : MEnsemble d α) : NNReal :=
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

variable {ψ : Ket d}

/-- A pure-state ensemble mixes into a pure state if and only if
the only states in the ensemble with nonzero probability are equal to `ψ`  -/
theorem mix_pEnsemble_pure_iff_pure {e : PEnsemble d α} :
  mix (toMEnsemble e) = MState.pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = ψ := by
  sorry

/-- The average of `f : Ket d → T` on an ensemble that mixes to a pure state `ψ` is `f ψ` -/
theorem mix_pEnsemble_pure_average {e : PEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U]
    [inst : Mixable U T] (f : Ket d → T) (hmix : mix (toMEnsemble e) = MState.pure ψ) :
  pure_average f e = f ψ := by
  have hpure := mix_pEnsemble_pure_iff_pure.mp hmix
  simp only [pure_average, Functor.map, Distribution.expect_val]
  apply Mixable.to_U_inj
  rw [PEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply]
  have h1 : ∀ i ∈ Finset.univ, (e.distr i : ℝ) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (e.distr i : ℝ) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.coe_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  classical rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  classical conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  classical conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = ψ := fun i hi hne0 ↦ by
    apply hpure i
    simpa using hne0
  classical rw [←Finset.sum_smul, ←Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

theorem sum_prob_mul_eq_one_iff {ι : Type*} [Fintype ι] (p : ι → ℝ) (x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hx : ∀ i, x i ≤ 1) :
    (∑ i, p i * x i = 1) ↔ ∀ i, p i ≠ 0 → x i = 1 := by
  constructor
  · intro a i a_1
    contrapose! a
    have h : ∃ i, p i * x i < p i := by
      use i
      apply mul_lt_of_lt_one_right
      · exact lt_of_le_of_ne' (hp i) a_1
      · exact lt_of_le_of_ne (hx i) a
    replace h : ∑ i, p i * x i < ∑ i, p i :=
      Finset.sum_lt_sum (fun i _ ↦ by nlinarith [hp i, hx i]) (by simpa using h)
    exact (h.trans_le (by simp [hsum])).ne
  · intro a
    rw [← hsum]
    congr! with i
    by_cases hi : p i = 0
    · simp [hi]
    · simp [a i hi]

--CLEANUP. This proof works but it takes forever to build. Too long.
theorem MState.exp_val_pure_eq_one_iff {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) (ψ : Ket d) :
    ρ.exp_val (pure ψ) = 1 ↔ ρ = pure ψ := by
  stop
  constructor <;> intro h <;> simp_all +decide [ MState.exp_val ];
  · have h_eq : ρ.M = (MState.pure ψ).M := by
      have h_eq : (ρ.M - (MState.pure ψ).M).inner (ρ.M - (MState.pure ψ).M) = 0 := by
        have h_eq_inner : (ρ.M - (MState.pure ψ).M).inner (ρ.M - (MState.pure ψ).M) = ρ.M.inner ρ.M - 2 * ρ.M.inner (MState.pure ψ).M + (MState.pure ψ).M.inner (MState.pure ψ).M := by
          norm_num [ HermitianMat.inner, Matrix.mul_apply ];
          simp +decide [ Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm ( ρ.m ) ];
          ring;
        have h_eq_inner : ρ.M.inner ρ.M ≤ 1 ∧ (MState.pure ψ).M.inner (MState.pure ψ).M = 1 := by
          aesop;
          · have := ρ.M.inner_le_mul_trace ρ.zero_le ρ.zero_le;
            aesop;
          · simp +decide [ HermitianMat.inner ];
            have := MState.pure_mul_self ψ; aesop;
        have h_eq_inner : (ρ.M - (MState.pure ψ).M).inner (ρ.M - (MState.pure ψ).M) ≥ 0 := by
          exact?;
        linarith;
      have h_eq : ∀ (A : HermitianMat d ℂ), A.inner A = 0 → A = 0 := by
        intro A hA;
        exact?;
      exact sub_eq_zero.mp ( h_eq _ ‹_› );
    cases ρ ; cases ψ ; aesop;
  · unfold HermitianMat.inner; aesop;
    rw [ MState.pure_mul_self ] ; aesop

theorem mix_mEnsemble_pure_iff_pure {e : MEnsemble d α} :
    mix e = pure ψ ↔ ∀ i : α, e.distr i ≠ 0 → e.states i = MState.pure ψ := by
  have h : (mix e).exp_val ↑(MState.pure ψ) = ∑ i, ↑(e.distr i) * (e.states i).exp_val ↑(MState.pure ψ) := by
    simp [MState.exp_val, HermitianMat.inner_def, Finset.sum_mul]
  rw [← MState.exp_val_pure_eq_one_iff, h, sum_prob_mul_eq_one_iff]
  · simp only [MState.exp_val_pure_eq_one_iff, ne_eq, Set.Icc.coe_eq_zero]
  · exact fun i => ( e.distr i ).2.1;
  · simp
  · intro i
    apply (e.states i).exp_val_le_one (MState.le_one _)

/-- The average of `f : MState d → T` on an ensemble that mixes to a pure state `ψ` is `f (pure ψ)` -/
theorem mix_mEnsemble_pure_average {e : MEnsemble d α} {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (hmix : mix e = pure ψ) :
  average f e = f (pure ψ) := by
  have hpure := mix_mEnsemble_pure_iff_pure.mp hmix
  simp only [average, Functor.map, Distribution.expect_val]
  apply Mixable.to_U_inj
  rw [MEnsemble.states] at hpure
  simp only [Mixable.to_U_of_mkT, Function.comp_apply]
  have h1 : ∀ i ∈ Finset.univ, (e.distr i : ℝ) • (Mixable.to_U (f (e.var i))) ≠ 0 → e.var i = pure ψ := fun i hi ↦ by
    have h2 : e.distr i = 0 → (e.distr i : ℝ) • (Mixable.to_U (f (e.var i))) = 0 := fun h0 ↦ by
      simp only [h0, Prob.coe_zero, zero_smul]
    exact (hpure i) ∘ h2.mt
  classical rw [←Finset.sum_filter_of_ne h1, Finset.sum_filter]
  classical conv =>
    enter [1, 2, a]
    rw [←dite_eq_ite]
    enter [2, hvar]
    rw [hvar]
  classical conv =>
    enter [1, 2, a]
    rw [dite_eq_ite]
    rw [←ite_zero_smul]
  have hpure' : ∀ i ∈ Finset.univ, (↑(e.distr i) : ℝ) ≠ 0 → e.var i = pure ψ := fun i hi hne0 ↦ by
    apply hpure i
    simpa using hne0
  classical rw [← Finset.sum_smul, ← Finset.sum_filter, Finset.sum_filter_of_ne hpure', Distribution.normalized, one_smul]

/-- The trivial mixed-state ensemble of `ρ` consists of copies of `rho`, with the `i`-th one having
probability 1. -/
def trivial_mEnsemble (ρ : MState d) (i : α) : MEnsemble d α := ⟨fun _ ↦ ρ, Distribution.constant i⟩

/-- The trivial mixed-state ensemble of `ρ` mixes to `ρ` -/
theorem trivial_mEnsemble_mix (ρ : MState d) : ∀ i : α, mix (trivial_mEnsemble ρ i) = ρ := fun i ↦by
  apply MState.ext_m
  classical simp only [trivial_mEnsemble, Distribution.constant, mix_of, DFunLike.coe, apply_ite,
    Prob.coe_one, Prob.coe_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- The average of `f : MState d → T` on a trivial ensemble of `ρ` is `f ρ`-/
theorem trivial_mEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : MState d → T) (ρ : MState d):
  ∀ i : α, average f (trivial_mEnsemble ρ i) = f ρ := fun i ↦ by
    simp only [average, Functor.map, Distribution.expect_val, trivial_mEnsemble]
    apply Mixable.to_U_inj
    classical simp [apply_ite]

instance MEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (MEnsemble d α) where
  default := trivial_mEnsemble default default

/-- The trivial pure-state ensemble of `ψ` consists of copies of `ψ`, with the `i`-th one having
probability 1. -/
def trivial_pEnsemble (ψ : Ket d) (i : α) : PEnsemble d α := ⟨fun _ ↦ ψ, Distribution.constant i⟩

variable (ψ : Ket d)

/-- The trivial pure-state ensemble of `ψ` mixes to `ψ` -/
theorem trivial_pEnsemble_mix : ∀ i : α, mix (toMEnsemble (trivial_pEnsemble ψ i)) = MState.pure ψ := fun i ↦ by
  apply MState.ext_m
  classical simp only [trivial_pEnsemble, Distribution.constant, toMEnsemble_mk, mix_of, DFunLike.coe,
    apply_ite, Prob.coe_one, Prob.coe_zero, MEnsemble.states, Function.comp_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

omit [DecidableEq d] in
/-- The average of `f : Ket d → T` on a trivial ensemble of `ψ` is `f ψ`-/
theorem trivial_pEnsemble_average {T : Type _} {U : Type*} [AddCommGroup U] [Module ℝ U] [inst : Mixable U T] (f : Ket d → T) :
  ∀ i : α, pure_average f (trivial_pEnsemble ψ i) = f ψ := fun i ↦ by
    simp only [pure_average, Functor.map, Distribution.expect_val, trivial_pEnsemble]
    apply Mixable.to_U_inj
    classical simp [apply_ite]

instance PEnsemble.instInhabited [Nonempty d] [Inhabited α] : Inhabited (PEnsemble d α) where
  default := trivial_pEnsemble default default

/-- The spectral pure-state ensemble of `ρ`. The states are its eigenvectors, and the probabilities, eigenvalues. -/
def spectral_ensemble (ρ : MState d) : PEnsemble d d where
  var i :=
    { vec := ρ.Hermitian.eigenvectorBasis i
      normalized' := by
        rw [←one_pow 2, ←ρ.Hermitian.eigenvectorBasis.orthonormal.1 i]
        have hnonneg : 0 ≤ ∑ x : d, Complex.normSq (ρ.Hermitian.eigenvectorBasis i x) := by
          simp_rw [Complex.normSq_eq_norm_sq]
          positivity
        simp only [← Complex.normSq_eq_norm_sq, EuclideanSpace.norm_eq, Real.sq_sqrt hnonneg]
    }
  distr := ρ.spectrum

--PULLOUT
theorem spectral_decomposition_sum {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i) • (Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i))) := by
  nth_rw 1 [hA.spectral_theorem]
  ext
  simp only [Matrix.sum_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMulVec, Algebra.smul_def, mul_comm, mul_left_comm]

/-- The spectral pure-state ensemble of `ρ` mixes to `ρ` -/
theorem spectral_ensemble_mix {ρ : MState d} : mix (↑(spectral_ensemble ρ) : MEnsemble d d) = ρ := by
  ext i j
  convert rfl;
  convert rfl;
  apply MState.ext_m;
  convert Ensemble.mix_of _
  convert (spectral_decomposition_sum ρ.Hermitian) using 1

end Ensemble
