/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Leonardo A. Lessa
-/
import QuantumInfo.ForMathlib
import ClassicalInfo.Distribution
import QuantumInfo.Finite.Braket

import Mathlib.Logic.Equiv.Basic

/-!
Finite dimensional quantum mixed states, ρ.

The same comments apply as in `Braket`:

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.

Important definitions:
 * `instMixable`: the `Mixable` instance allowing convex combinations of `MState`s
 * `ofClassical`: Mixed states representing classical distributions
 * `purity`: The purity `Tr[ρ^2]` of a state
 * `spectrum`: The spectrum of the matrix
 * `uniform`: The maximally mixed state
 * `mix`: The total state corresponding to an ensemble
 * `average`: Averages a function over an ensemble, with appropriate weights
-/

noncomputable section

open BigOperators
open ComplexConjugate
open HermitianMat
open scoped Matrix ComplexOrder

/-- A **mixed quantum state** is a PSD matrix with trace 1.

We don't `extend (M : HermitianMat d ℂ)` because that gives an annoying thing where
`M` is actually a `Subtype`, which means `ρ.M.foo` notation doesn't work. -/
@[ext]
structure MState (d : Type*) [Fintype d] [DecidableEq d] where
  M : HermitianMat d ℂ
  zero_le : 0 ≤ M
  tr : M.trace = 1

namespace MState

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]

attribute [coe] MState.M
instance instCoe : Coe (MState d) (HermitianMat d ℂ) := ⟨MState.M⟩

attribute [simp] MState.tr

/-- The underlying `Matrix` in an MState. Prefer `MState.M` for the `HermitianMat`. -/
def m (ρ : MState d) : Matrix d d ℂ := ρ.M.toMat

@[simp]
theorem toMat_M (ρ : MState d) : ρ.M.toMat = ρ.m := by
  rfl

--XXX These are methods that directly reference the matrix, "m" or ".val".
-- We'd like to remove these (where possible) so that mostly go through HermitianMat
-- where possible.
theorem pos (ρ : MState d) : ρ.m.PosSemidef :=
  HermitianMat.zero_le_iff.mp ρ.zero_le

/-- Every mixed state is Hermitian. -/
theorem Hermitian (ρ : MState d) : ρ.m.IsHermitian :=
  ρ.pos.left

@[simp]
theorem tr' (ρ : MState d) : ρ.m.trace = 1 := by
  rw [MState.m.eq_def, ← HermitianMat.trace_eq_trace_rc, ρ.tr]
  simp

theorem ext_m {ρ₁ ρ₂ : MState d} (h : ρ₁.m = ρ₂.m) : ρ₁ = ρ₂ := by
  rw [MState.mk.injEq]
  ext1
  exact h
--XXX

/-- The map from mixed states to their matrices is injective -/
theorem toMat_inj : (MState.m (d := d)).Injective :=
  fun _ _ h ↦ by ext1; ext1; exact h

theorem M_Injective : Function.Injective (MState.M (d := d)) := by
  intro _ _
  exact MState.ext

variable (d) in
/-- The matrices corresponding to MStates are `Convex ℝ` -/
theorem convex : Convex ℝ (Set.range (MState.M (d := d))) := by
  simp only [Convex, Set.mem_range, StarConvex,
    forall_exists_index, forall_apply_eq_imp_iff]
  intro x y a b ha hb hab
  replace hab : a + b = (1 : ℂ) := by norm_cast
  have := HermitianMat.convex_cone x.zero_le y.zero_le ha hb
  exact ⟨⟨_, this, by simpa using mod_cast hab⟩, rfl⟩

instance instMixable : Mixable (HermitianMat d ℂ) (MState d) where
  to_U := MState.M
  to_U_inj := MState.ext
  mkT {u} := fun h ↦
    ⟨⟨u, h.casesOn fun t ht ↦ ht ▸ t.zero_le,
      h.casesOn fun t ht ↦ ht ▸ t.tr⟩, rfl⟩
  convex := convex d

--An MState is a witness that d is nonempty.
instance nonempty (ρ : MState d) : Nonempty d := by
  by_contra h
  simpa [HermitianMat.trace_eq_re_trace, not_nonempty_iff.mp h] using ρ.tr

-- Could have used properties of ρ.spectrum
theorem eigenvalue_nonneg (ρ : MState d) : ∀ i, 0 ≤ ρ.Hermitian.eigenvalues i := by
  apply (Matrix.PosSemidef.nonneg_iff_eigenvalue_nonneg ρ.Hermitian).mp
  exact ρ.zero_le

-- Could have used properties of  ρ.spectrum
theorem eigenvalue_le_one (ρ : MState d) : ∀ i, ρ.Hermitian.eigenvalues i ≤ 1 := by
  intro i
  convert Finset.single_le_sum (fun y _ ↦ ρ.pos.eigenvalues_nonneg y) (Finset.mem_univ i)
  rw [ρ.M.sum_eigenvalues_eq_trace, ρ.tr]

theorem le_one (ρ : MState d) : ρ.M ≤ 1 := by
  open MatrixOrder in
  rw [Subtype.mk_le_mk]
  simp only [HermitianMat.val_eq_coe, selfAdjoint.val_one]
  suffices h : ρ.m ≤ (1 : ℝ) • 1 by
    rw [one_smul] at h
    exact h
  apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ρ.pos.1 1).mp
  exact eigenvalue_le_one ρ

/-- The inner product of two MState's, as a real number between 0 and 1. -/
def inner (ρ : MState d) (σ : MState d) : Prob :=
  ⟨ρ.M.inner σ.M, ρ.M.inner_ge_zero ρ.zero_le σ.zero_le,
    (ρ.M.inner_le_mul_trace ρ.zero_le σ.zero_le).trans (by simp)⟩

--TODO: Should we actually switch to use `Inner.inner` in a better way here? But I don't
--want to have to write `⟪ρ, σ⟫_Prob` each time.
@[inherit_doc]
scoped[MState] notation:max "⟪" x ", " y "⟫" => MState.inner x y

section exp_val

def exp_val_ℂ (ρ : MState d) (T : Matrix d d ℂ) : ℂ :=
  (T * ρ.m).trace

--TODO: Bundle as a ContinuousLinearMap.
/-- The **expectation value** of an operator on a quantum state. -/
def exp_val (ρ : MState d) (T : HermitianMat d ℂ) : ℝ :=
  ρ.M.inner T

theorem exp_val_nonneg {T : HermitianMat d ℂ} (h : 0 ≤ T) (ρ : MState d) : 0 ≤ ρ.exp_val T :=
  HermitianMat.inner_ge_zero ρ.zero_le h

@[simp]
theorem exp_val_zero (ρ : MState d) : ρ.exp_val 0 = 0 := by
  simp [MState.exp_val]

@[simp]
theorem exp_val_one (ρ : MState d) : ρ.exp_val 1 = 1 := by
  simp [MState.exp_val]

theorem exp_val_le_one {T : HermitianMat d ℂ} (h : T ≤ 1) (ρ : MState d) : ρ.exp_val T ≤ 1 := by
  have hmono := HermitianMat.inner_mono ρ.zero_le h
  rwa [HermitianMat.inner_one ρ.M, ρ.tr] at hmono

theorem exp_val_prob {T : HermitianMat d ℂ} (h : 0 ≤ T ∧ T ≤ 1) (ρ : MState d) :
    0 ≤ ρ.exp_val T ∧ ρ.exp_val T ≤ 1 :=
  ⟨ρ.exp_val_nonneg h.1, ρ.exp_val_le_one h.2⟩

theorem exp_val_sub (ρ : MState d) (A B : HermitianMat d ℂ) :
    ρ.exp_val (A - B) = ρ.exp_val A - ρ.exp_val B := by
  simp [exp_val, HermitianMat.inner_left_sub]

/-- If a PSD observable `A` has expectation value of 0 on a state `ρ`, it must entirely contain the
support of `ρ` in its kernel. -/
theorem exp_val_eq_zero_iff (ρ : MState d) {A : HermitianMat d ℂ} (hA₁ : 0 ≤ A)   :
    ρ.exp_val A = 0 ↔ ρ.M.support ≤ A.ker := by
  exact ρ.M.inner_zero_iff ρ.zero_le hA₁

/-- If an observable `A` has expectation value of 1 on a state `ρ`, it must entirely contain the
support of `ρ` in its 1-eigenspace. -/
theorem exp_val_eq_one_iff (ρ : MState d) {A : HermitianMat d ℂ} (hA₂ : A ≤ 1) :
    ρ.exp_val A = 1 ↔ ρ.M.support ≤ (1 - A).ker := by
  rw [← exp_val_eq_zero_iff ρ (A := 1 - A) (HermitianMat.zero_le_iff.mpr hA₂)]
  rw [exp_val_sub, exp_val_one]
  rw [sub_eq_zero, eq_comm]

theorem exp_val_add (ρ : MState d) (A B : HermitianMat d ℂ) :
    ρ.exp_val (A + B) = ρ.exp_val A + ρ.exp_val B := by
  simp [MState.exp_val, HermitianMat.inner_left_distrib]

@[simp]
theorem exp_val_smul (ρ : MState d) (r : ℝ) (A : HermitianMat d ℂ) :
    ρ.exp_val (r • A) = r * ρ.exp_val A := by
  simp [MState.exp_val]

@[gcongr]
theorem exp_val_le_exp_val (ρ : MState d) {A B : HermitianMat d ℂ} (h : A ≤ B) :
    ρ.exp_val A ≤ ρ.exp_val B := by
  simp only [MState.exp_val]
  refine ρ.M.inner_mono ρ.zero_le h

end exp_val

section pure

/-- A mixed state can be constructed as a pure state arising from a ket. -/
def pure (ψ : Ket d) : MState d where
  M := {
    val := Matrix.vecMulVec ψ (ψ : Bra d)
    property := (Matrix.PosSemidef.outer_self_conj ψ).1
  }
  zero_le := HermitianMat.zero_le_iff.mpr (.outer_self_conj ψ)
  tr := by
    have h₁ (x) : ψ x * conj (ψ x) = Complex.normSq (ψ x) := by
      rw [mul_comm, Complex.normSq_eq_conj_mul_self]
    simp [HermitianMat.trace_eq_re_trace, Matrix.trace, Matrix.vecMulVec_apply, Bra.eq_conj, h₁]
    exact ψ.normalized

proof_wanted pure_inner (ψ φ : Ket d) : ⟪pure ψ, pure φ⟫ = ‖Braket.dot ψ φ‖^2

@[simp]
theorem pure_apply {i j : d} (ψ : Ket d) : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

theorem pure_mul_self (ψ : Ket d) : (pure ψ).m * (pure ψ).m = (pure ψ : Matrix d d ℂ) := by
  dsimp [pure, MState.m, HermitianMat.toMat]
  simp [Matrix.vecMulVec_mul_vecMulVec, ← Braket.dot_eq_dotProduct]

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always between zero and one. -/
def purity (ρ : MState d) : Prob := ⟪ρ, ρ⟫

/-- The eigenvalue spectrum of a mixed quantum state, as a `Distribution`. -/
def spectrum [DecidableEq d] (ρ : MState d) : Distribution d :=
  Distribution.mk'
    (ρ.M.H.eigenvalues ·)
    (ρ.pos.eigenvalues_nonneg ·)
    (by rw [ρ.M.sum_eigenvalues_eq_trace, ρ.tr])

/-- The specturm of a pure state is (1,0,0,...), i.e. a constant distribution. -/
theorem spectrum_pure_eq_constant (ψ : Ket d) :
    ∃ i, (pure ψ).spectrum = Distribution.constant i := by
  let ρ := pure ψ
  -- Prove 1 is in the spectrum of pure ψ by exhibiting an eigenvector with value 1.
  have : ∃i, (pure ψ).spectrum i = 1 := by
    simp [spectrum, Distribution.mk']
    have hEig : ∃i, (pure ψ).M.H.eigenvalues i = 1 := by
      -- Prove ψ is an eigenvector of ρ = pure ψ
      have hv : ρ.M *ᵥ ψ = ψ := by
        ext
        simp_rw [ρ, pure, Matrix.mulVec, HermitianMat.toMat, Matrix.vecMulVec_apply, dotProduct,
        Bra.apply', Ket.apply, mul_assoc, ← Finset.mul_sum, ← Complex.normSq_eq_conj_mul_self,
        ← Complex.ofReal_sum, ← Ket.apply, ψ.normalized, Complex.ofReal_one, mul_one]
      let U : Matrix.unitaryGroup d ℂ := star ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
      let w : d → ℂ := U *ᵥ ψ
      -- Prove w = U ψ is an eigenvector of the diagonalized matrix of ρ = pure ψ
      have hDiag : Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) *ᵥ w = w := by
        simp_rw [←Matrix.IsHermitian.star_mul_self_mul_eq_diagonal, eq_comm,
        ←Matrix.mulVec_mulVec, w, U, Matrix.mulVec_mulVec] -- Uses spectral theorem
        simp_all
        rw [←Matrix.mulVec_mulVec, hv]
      -- Prove w = U ψ is nonzero by contradiction
      have hwNonZero : ∃j, w j ≠ 0 := by
        by_contra hwZero
        simp at hwZero
        rw [←funext_iff] at hwZero
        -- If w is zero, then ψ is zero, since U is invertible
        have hψZero : ∀x, ψ x = 0 := by
          apply congr_fun
          -- Prove U is invertible
          have hUdetNonZero : (U : Matrix d d ℂ).det ≠ 0 := by
            by_contra hDetZero
            obtain ⟨u, huUni⟩ := U
            have h0uni: 0 ∈ unitary ℂ := by
              rw [←hDetZero]
              simp
              exact Matrix.det_of_mem_unitary huUni
            rw [unitary.mem_iff] at h0uni
            simp_all
          exact Matrix.eq_zero_of_mulVec_eq_zero hUdetNonZero hwZero
        -- Reach an contradiction that ψ has norm 0
        have hψn := Ket.normalized ψ
        have hnormZero : ∀ x : d, Complex.normSq (ψ x) = 0 := fun x => by
          rw [hψZero x, Complex.normSq_zero]
        have hsumZero : ∑ x : d, Complex.normSq (ψ x) = 0 := by
          apply Finset.sum_eq_zero
          intros x _
          exact hnormZero x
        simp_all
      obtain ⟨j, hwNonZero'⟩ := hwNonZero
      have hDiagj := congr_fun hDiag j
      rw [Matrix.mulVec_diagonal, mul_eq_right₀ hwNonZero'] at hDiagj
      use j
      simp_all
    obtain ⟨i, hEig'⟩ := hEig
    use i
    ext
    exact hEig'
  --If 1 is in a distribution, the distribution is a constant.
  obtain ⟨i, hi⟩ := this
  use i
  exact Distribution.constant_of_exists_one hi

/-- If the specturm of a mixed state is (1,0,0...) i.e. a constant distribution, it is
 a pure state. -/
theorem pure_of_constant_spectrum (ρ : MState d) (h : ∃ i, ρ.spectrum = Distribution.constant i) :
    ∃ ψ, ρ = pure ψ := by
  obtain ⟨i, h'⟩ := h
  -- Translate assumption to eigenvalues being (1,0,0,...)
  have hEig : ρ.M.H.eigenvalues = fun x => if x = i then 1 else 0 := by
    ext x
    simp [spectrum, Distribution.constant, Distribution.mk'] at h'
    rw [Subtype.mk.injEq] at h'
    have h'x := congr_fun h' x
    rw [if_congr (Eq.comm) (Eq.refl 1) (Eq.refl 0)]
    rw [Prob.eq_iff] at h'x
    dsimp at h'x
    rw [h'x]
    split_ifs
    case pos => rfl
    case neg => rfl
  -- Choose the eigenvector v of ρ with eigenvalue 1 to make ψ
  let ⟨u, huUni⟩ := ρ.M.H.eigenvectorUnitary -- Diagonalizing unitary of ρ
  let D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ ρ.M.H.eigenvalues) -- Diagonal matrix of ρ
  let v : EuclideanSpace ℂ d := ρ.M.H.eigenvectorBasis i
  -- Prove v is normalized
  have hUvNorm : ∑ x, ‖v x‖^2 = 1 := by
    have hinnerv : Inner.inner ℂ v v = 1 := by
      have := ρ.M.H.eigenvectorBasis.orthonormal
      rw [orthonormal_iff_ite] at this
      convert this i i
      simp
    simp only [PiLp.inner_apply, RCLike.inner_apply, Complex.mul_conj'] at hinnerv
    rw [← Fintype.sum_equiv (Equiv.refl d) _ (fun x => (Complex.ofReal ‖v x‖) ^ 2) (fun x => Complex.ofReal_pow ‖v x‖ 2)] at hinnerv
    rw [← Complex.ofReal_sum Finset.univ (fun x => ‖v x‖ ^ 2), Complex.ofReal_eq_one] at hinnerv
    exact hinnerv
  let ψ : Ket d := ⟨v, hUvNorm⟩ -- Construct ψ
  use ψ
  ext j k
  -- Use spectral theorem to prove that ρ = pure ψ
  rw [Matrix.IsHermitian.spectral_theorem ρ.M.H, Matrix.mul_apply]
  simp [ψ, v, hEig, -toMat_M]
  have hsum : ∀ x ∈ Finset.univ, x ∉ ({i} : Finset d) → (ρ.M.H.eigenvectorBasis x j) * (↑(if x = i then 1 else 0) : ℝ) * (starRingEnd ℂ) (ρ.Hermitian.eigenvectorBasis x k) = 0 := by
    intros x hx hxnoti
    rw [Finset.mem_singleton] at hxnoti
    rw [if_neg hxnoti, Complex.ofReal_zero]
    ring
  simp_rw [←Finset.sum_subset (Finset.subset_univ {i}) hsum, Finset.sum_singleton, reduceIte, Complex.ofReal_one, mul_one]
  rfl

/-- A state ρ is pure iff its spectrum is (1,0,0,...) i.e. a constant distribution. -/
theorem pure_iff_constant_spectrum (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔
    ∃ i, ρ.spectrum = Distribution.constant i :=
  ⟨fun h ↦ h.rec fun ψ h₂ ↦ h₂ ▸ spectrum_pure_eq_constant ψ,
  pure_of_constant_spectrum ρ⟩

theorem pure_iff_purity_one (ρ : MState d) : (∃ ψ, ρ = pure ψ) ↔ ρ.purity = 1 := by
  --purity = exp(-Collision entropy)
  --purity eq 1 iff collision entropy is zero
  --entropy is zero iff distribution is constant
  --distribution is constant iff pure
  constructor <;> intro h;
  · obtain ⟨w, h⟩ := h
    subst h
    unfold MState.purity;
    unfold MState.inner;
    unfold HermitianMat.inner;
    -- Since the product of the pure state with itself is the pure state itself, the trace of this product is the same as the trace of the pure state.
    have h_trace : Matrix.trace ((MState.pure w).M.toMat * (MState.pure w).M.toMat) = Matrix.trace (MState.pure w).M.toMat := by
      convert congr_arg Matrix.trace ( MState.pure_mul_self w );
    aesop;
  · -- Apply the theorem that states a mixed state is pure if and only if its spectrum is constant.
    apply (pure_iff_constant_spectrum ρ).mpr;
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val ^ 2 = 1 := by
      -- By definition of purity, we know that the sum of the squares of the eigenvalues is equal to the trace of ρ squared.
      have h_trace_sq : ∑ i, (ρ.spectrum i).val ^ 2 = ρ.purity := by
        have h_eigenvalues : ∑ i, (ρ.M.H.eigenvalues i) ^ 2 = Matrix.trace (ρ.M.toMat * ρ.M.toMat) := by
          have := Matrix.IsHermitian.spectral_theorem ρ.M.H;
          conv_rhs => rw [ this ];
          simp [ Matrix.trace_mul_comm, Matrix.mul_assoc ];
          exact Finset.sum_congr rfl fun _ _ => by ring;
        convert congr_arg Complex.re h_eigenvalues using 1;
      aesop;
    have h_eigenvalues : ∑ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) = 0 := by
      simp_all [ sq, mul_sub ];
    -- Since each term in the sum is non-positive and their sum is zero, each term must be zero.
    have h_each_zero : ∀ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) = 0 := by
      have h_each_zero : ∀ i, (ρ.spectrum i).val * ((ρ.spectrum i).val - 1) ≤ 0 := by
        exact fun i => by nlinarith only [ show ( ρ.spectrum i : ℝ ) ≥ 0 by exact_mod_cast ( ρ.spectrum i ) |>.2.1, show ( ρ.spectrum i : ℝ ) ≤ 1 by exact_mod_cast ( ρ.spectrum i ) |>.2.2 ] ;
      exact fun i => le_antisymm ( h_each_zero i ) ( by simpa [ h_eigenvalues ] using Finset.single_le_sum ( fun i _ => neg_nonneg.mpr ( h_each_zero i ) ) ( Finset.mem_univ i ) );
    -- Since each term in the sum is non-positive and their sum is zero, each term must be zero. Therefore, for each i, either (ρ.spectrum i).val = 0 or (ρ.spectrum i).val = 1.
    have h_each_zero : ∀ i, (ρ.spectrum i).val = 0 ∨ (ρ.spectrum i).val = 1 := by
      exact fun i => mul_eq_zero.mp ( h_each_zero i ) |> Or.imp id fun h => by linarith;
    have h_sum_one : ∑ i, (ρ.spectrum i).val = 1 := by
      grind;
    obtain ⟨i, hi⟩ : ∃ i, (ρ.spectrum i).val = 1 := by
      contrapose! h_sum_one; aesop;
    -- Since the sum of the eigenvalues is 1 and one of them is 1, the remaining eigenvalues must sum to 0. Given that each eigenvalue is either 0 or 1, the only way their sum can be 0 is if all of them are 0.
    have h_sum_zero : ∑ j ∈ Finset.univ.erase i, (ρ.spectrum j).val = 0 := by
      rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ i ), hi ] at h_sum_one ; linarith;
    rw [ Finset.sum_eq_zero_iff_of_nonneg ] at h_sum_zero <;> aesop

--PULLOUT
theorem _root_.Matrix.unitaryGroup_row_norm (U : Matrix.unitaryGroup d ℂ) (i : d) :
    ∑ j, ‖U j i‖^2 = 1 := by
  suffices ∑ j, ‖U j i‖^2 = (1 : ℂ) by exact_mod_cast this
  simpa [Matrix.mul_apply, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    using congr($(U.prop.left) i i)

--TODO: Would be better if there was an `MState.eigenstate` or similar (maybe extending
-- a similar thing for `HermitianMat`) and then this could be an equality with that, as
-- an explicit formula, instead of this `Exists`.
theorem spectralDecomposition (ρ : MState d) :
    ∃ (ψs : d → Ket d), ρ.M = ∑ i, (ρ.spectrum i : ℝ) • (MState.pure (ψs i)).M := by
  use (fun i ↦ ⟨(ρ.M.H.eigenvectorUnitary · i), Matrix.unitaryGroup_row_norm _ i⟩)
  ext i j
  nth_rw 1 [ρ.M.H.spectral_theorem]
  simp only [toMat_M, Complex.coe_algebraMap, spectrum, Distribution.mk',
    Distribution.funlike_apply, pure, Matrix.IsHermitian.eigenvectorUnitary_apply,
    PiLp.ofLp_apply, AddSubgroup.val_finset_sum, val_eq_coe, selfAdjoint.val_smul]
  rw [Finset.sum_apply, Finset.sum_apply, Matrix.mul_apply]
  congr!
  simp [Matrix.vecMulVec_apply, Ket.apply, Matrix.mul_diagonal]
  ac_rfl

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  M := ρ₁.M ⊗ₖ ρ₂.M
  zero_le := HermitianMat.zero_le_iff.mpr (ρ₁.pos.PosSemidef_kronecker ρ₂.pos)
  tr := by simp

infixl:100 " ⊗ " => MState.prod

theorem prod_inner_prod (ξ1 ψ1 : MState d₁) (ξ2 ψ2 : MState d₂) :
    ⟪ξ1 ⊗ ξ2, ψ1 ⊗ ψ2⟫ = ⟪ξ1, ψ1⟫ * ⟪ξ2, ψ2⟫ := by
  ext1
  simp only [MState.inner, Prob.coe_mul, ← Complex.ofReal_inj]
  --Lots of this should actually be facts about HermitianMat first
  simp only [prod, Complex.ofReal_mul]
  simp only [← RCLike.ofReal_eq_complex_ofReal, inner_eq_trace_rc]
  simp only [kronecker, ← Matrix.trace_kronecker]
  simp only [Matrix.mul_kronecker_mul]

/-- The product of pure states is a pure product state , `Ket.prod`. -/
theorem pure_prod_pure (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : pure (ψ₁ ⊗ ψ₂) = (pure ψ₁) ⊗ (pure ψ₂) := by
  ext
  simp [Ket.prod, Ket.apply, prod, -toMat_apply]
  ac_rfl

end prod

/-- A representation of a classical distribution as a quantum state, diagonal in the given basis. -/
def ofClassical (dist : Distribution d) : MState d where
  M := HermitianMat.diagonal (fun x ↦ dist x)
  zero_le := HermitianMat.zero_le_iff.mpr (by simp [HermitianMat.diagonal, Matrix.posSemidef_diagonal_iff])
  tr := by simp [HermitianMat.trace_diagonal]

@[simp]
theorem coe_ofClassical (dist : Distribution d) :
    (MState.ofClassical dist).M = HermitianMat.diagonal (dist ·) := by
  rfl

theorem ofClassical_pow (dist : Distribution d) (p : ℝ) :
    (MState.ofClassical dist).M ^ p = HermitianMat.diagonal (fun i ↦ (dist i) ^ p) := by
  rw [coe_ofClassical]
  convert HermitianMat.diagonal_pow (dist ·) p

/-- The maximally mixed state. -/
def uniform [Nonempty d] : MState d := ofClassical Distribution.uniform

/-- There is exactly one state on a dimension-1 system. -/
--note that this still takes (and uses) the `Fintype d` and `DecidableEq d` instances on `MState d`.
--Even though instances for those can be derived from `Unique d`, we want this `Unique` instance to
--apply on `@MState d ?x ?y` for _any_ x and y.
instance instUnique [Unique d] : Unique (MState d) where
  default := @uniform _ _ _ _
  uniq := by
    intro ρ
    ext
    have h₁ := ρ.tr
    have h₂ := (@uniform _ _ _ _ : MState d).tr
    simp [Matrix.trace, Unique.eq_default, -MState.tr, HermitianMat.trace_eq_re_trace] at h₁ h₂ ⊢
    apply Complex.ext
    · exact h₁.trans h₂.symm
    · trans 0
      exact ρ.M.Complex_im_eq_zero default
      exact (uniform.M.Complex_im_eq_zero default).symm

/-- There exists a mixed state for every nonempty `d`.
Here, the maximally mixed one is chosen. -/
instance instInhabited [Nonempty d] : Inhabited (MState d) where
  default := uniform

section ptrace

-- TODO:
-- * Partial trace of direct product is the original state

/-- Partial tracing out the left half of a system. -/
def traceLeft (ρ : MState (d₁ × d₂)) : MState d₂ where
  M := ⟨ρ.m.traceLeft, ρ.M.H.traceLeft⟩
  zero_le :=  HermitianMat.zero_le_iff.mpr (ρ.pos.traceLeft)
  tr := by simp [trace]

/-- Partial tracing out the right half of a system. -/
def traceRight (ρ : MState (d₁ × d₂)) : MState d₁ where
  M := ⟨ρ.m.traceRight, ρ.M.H.traceRight⟩
  zero_le := HermitianMat.zero_le_iff.mpr (ρ.pos.traceRight)
  tr := by simp [trace]

/-- Taking the direct product on the left and tracing it back out gives the same state. -/
@[simp]
theorem traceLeft_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceLeft (ρ₁ ⊗ ρ₂) = ρ₂ := by
  ext
  simp_rw [traceLeft, Matrix.traceLeft, prod]
  have h : (∑ i : d₁, ρ₁.M.toMat i i) = 1 := ρ₁.tr'
  simp [MState.m, ← Finset.sum_mul, h, -toMat_M, -toMat_apply]

/-- Taking the direct product on the right and tracing it back out gives the same state. -/
@[simp]
theorem traceRight_prod_eq (ρ₁ : MState d₁) (ρ₂ : MState d₂) : traceRight (ρ₁ ⊗ ρ₂) = ρ₁ := by
  ext
  simp_rw [traceRight, Matrix.traceRight, prod]
  have h : (∑ i : d₂, ρ₂.M.toMat i i) = 1 := ρ₂.tr'
  simp [MState.m, ← Finset.mul_sum, h, -toMat_M, -toMat_apply]

end ptrace

-- TODO: direct sum (by zero-padding)

--TODO: Spectra of left- and right- partial traces of a pure state are equal.

set_option maxHeartbeats 0 in
--PULLOUT to Matrix.lean. Should be combined with `IsHermitian.cfc_eigenvalues`.
/-
If a Hermitian matrix A is unitarily similar to a diagonal matrix with real entries f, then the eigenvalues of A are a permutation of f.
-/
lemma Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal {d 𝕜 : Type*}
    [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.IsHermitian)
    {U : Matrix d d 𝕜} (hU : U ∈ Matrix.unitaryGroup d 𝕜)
    {f : d → ℝ}
    (h : A = U * Matrix.diagonal (fun i => (RCLike.ofReal (f i) : 𝕜)) * Matrix.conjTranspose U) :
    ∃ σ : d ≃ d, hA.eigenvalues ∘ σ = f := by
  -- Since A is unitarily similar to D, they have the same characteristic polynomial.
  have h_char_poly : Matrix.charpoly A = Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜)) := by
    have h_char_poly : Matrix.charpoly (U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.charpoly (Matrix.diagonal (fun i => (f i : 𝕜))) := by
      have h_det : ∀ (t : 𝕜), Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) := by
        intro t
        have h_det : Matrix.det (t • 1 - U * Matrix.diagonal (fun i => (f i : 𝕜)) * Uᴴ) = Matrix.det (U * (t • 1 - Matrix.diagonal (fun i => (f i : 𝕜))) * Uᴴ) := by
          simp [ mul_sub, sub_mul, Matrix.mul_assoc ];
          rw [ show U * Uᴴ = 1 from by simpa [ Matrix.mul_eq_one_comm ] using hU.2 ];
        have := congr_arg Matrix.det hU.2; norm_num at this; simp_all [ mul_assoc, mul_comm ] ;
        simp_all [ ← mul_assoc ];
        simp_all [ Star.star ]
      refine' Polynomial.funext fun t => _;
      convert h_det t using 1 <;> simp [ Matrix.charpoly, Matrix.det_apply' ];
      · simp [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
      · simp [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Matrix.one_apply ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
    rw [ h, h_char_poly ];
  -- The roots of the characteristic polynomial of A are its eigenvalues (by `IsHermitian.charpoly_roots_eq_eigenvalues`).
  have h_eigenvalues : (Matrix.charpoly A).roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
    exact Matrix.IsHermitian.roots_charpoly_eq_eigenvalues hA;
  -- The roots of the characteristic polynomial of D are the diagonal entries f.
  have h_diag_roots : (Matrix.charpoly (Matrix.diagonal fun i => (f i : 𝕜))).roots = Multiset.map (fun i => (f i : 𝕜)) Finset.univ.val := by
    simp [ Matrix.charpoly, Matrix.det_diagonal ];
    rw [ Polynomial.roots_prod ];
    · aesop;
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _;
  have := Multiset.map_univ_eq_iff ( RCLike.ofReal ∘ hA.eigenvalues ) f
  subst h
  simp_all only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, CompTriple.comp_eq]
  refine' this.mp _ |> fun ⟨ e, he ⟩ => ⟨ e.symm, _ ⟩
  · simpa [ Function.comp ] using congr_arg ( Multiset.map ( RCLike.re : 𝕜 → ℝ ) ) h_eigenvalues.symm
  · exact funext fun x => by simpa using congr_fun he ( e.symm x ) ;

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, MState.spectrum (ρ₁ ⊗ ρ₂) (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  by_contra! h;
  -- Apply `Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal` to $A \otimes B$ and $U_A \otimes U_B$ and the diagonal entries.
  obtain ⟨σ, hσ⟩ : ∃ σ : d₁ × d₂ ≃ d₁ × d₂, (ρ₁.prod ρ₂).M.H.eigenvalues ∘ σ = fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) := by
    have h_unitary : ∃ U : Matrix (d₁ × d₂) (d₁ × d₂) ℂ, U ∈ Matrix.unitaryGroup (d₁ × d₂) ℂ ∧ (ρ₁.prod ρ₂).M = U * Matrix.diagonal (fun (i, j) => ((ρ₁.spectrum i) * (ρ₂.spectrum j)) : d₁ × d₂ → ℂ) * Matrix.conjTranspose U := by
      -- Let $U_A$ and $U_B$ be the eigenvector unitaries of $\rho_1$ and $\rho_2$, respectively.
      obtain ⟨U_A, hU_A⟩ : ∃ U_A : Matrix d₁ d₁ ℂ, U_A ∈ Matrix.unitaryGroup d₁ ℂ ∧ ρ₁.M = U_A * Matrix.diagonal (fun i => (ρ₁.spectrum i : ℂ)) * Matrix.conjTranspose U_A := by
        have := ρ₁.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        grind
      obtain ⟨U_B, hU_B⟩ : ∃ U_B : Matrix d₂ d₂ ℂ, U_B ∈ Matrix.unitaryGroup d₂ ℂ ∧ ρ₂.M = U_B * Matrix.diagonal (fun j => (ρ₂.spectrum j : ℂ)) * Matrix.conjTranspose U_B := by
        have := ρ₂.M.H.spectral_theorem;
        refine' ⟨ _, _, this ⟩;
        grind;
      refine' ⟨ Matrix.kroneckerMap ( fun x y => x * y ) U_A U_B, _, _ ⟩;
      · simp_all [ Matrix.mem_unitaryGroup_iff ];
        have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = 1 := by
          have h_unitary : Matrix.kroneckerMap (fun x y => x * y) U_A U_B * Matrix.kroneckerMap (fun x y => x * y) (Star.star U_A) (Star.star U_B) = Matrix.kroneckerMap (fun x y => x * y) (U_A * Star.star U_A) (U_B * Star.star U_B) := by
            ext ⟨ i, j ⟩ ⟨ k, l ⟩ ; simp [ Matrix.mul_apply, Matrix.kroneckerMap_apply ]
            ring_nf
            erw [ Finset.sum_product ] ; simp [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
            exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
          aesop;
        convert h_unitary using 2;
        ext i j; simp [ Matrix.kroneckerMap ] ;
      · simp_all [ MState.prod, Matrix.mul_assoc, Matrix.mul_kronecker_mul ];
        congr 2;
        · ext ⟨ i, j ⟩ ⟨ i', j' ⟩ ; by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [ hi, hj ];
        · ext i j; simp [ Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply ] ;
    obtain ⟨ U, hU₁, hU₂ ⟩ := h_unitary;
    apply Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal;
    exact hU₁;
    convert hU₂ using 1;
    norm_num +zetaDelta at *;
  obtain ⟨ i, j, h ⟩ := h σ; have := congr_fun hσ ( i, j ) ; simp_all [ MState.spectrum ] ;
  exact h ( by exact Subtype.ext this )

theorem sInf_spectrum_prod (ρ : MState d) (σ : MState d₂) :
    sInf (_root_.spectrum ℝ (ρ ⊗ σ).m) = sInf (_root_.spectrum ℝ ρ.m) * sInf (_root_.spectrum ℝ σ.m) := by
  rcases isEmpty_or_nonempty d with _ | _; · simp
  rcases isEmpty_or_nonempty d₂ with _ | _; · simp
  rw [MState.m, MState.prod, HermitianMat.spectrum_prod, ← MState.m, ← MState.m]
  apply csInf_mul_nonneg
  · exact IsSelfAdjoint.spectrum_nonempty ρ.M.H
  · rw [MState.m, ρ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply ρ.eigenvalue_nonneg
  · exact IsSelfAdjoint.spectrum_nonempty σ.M.H
  · rw [MState.m, σ.M.H.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    apply σ.eigenvalue_nonneg

--TODO: Spectrum of direct sum. Spectrum of partial trace?

/-- A mixed state is separable iff it can be written as a convex combination of product mixed states. -/
def IsSeparable (ρ : MState (d₁ × d₂)) : Prop :=
  ∃ ρLRs : Finset (MState d₁ × MState d₂), --Finite set of (ρL, ρR) pairs
    ∃ ps : Distribution ρLRs, --Distribution over those pairs, an ensemble
      ρ.M = ∑ ρLR : ρLRs, (ps ρLR : ℝ) • (Prod.fst ρLR.val).M ⊗ₖ (Prod.snd ρLR.val).M

/-- A product state `MState.prod` is separable. -/
theorem IsSeparable_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : IsSeparable (ρ₁ ⊗ ρ₂) := by
  let only := (ρ₁, ρ₂)
  use { only }, Distribution.constant ⟨only, Finset.mem_singleton_self only⟩
  simp [prod, Unique.eq_default, only]

theorem eq_of_sum_eq_pure {d : Type*} [Fintype d] [DecidableEq d]
    {ι : Type*} {s : Finset ι} {p : ι → ℝ} {ρs : ι → MState d}
    {ρ : MState d} (h_pure : ρ.purity = 1) (h_sum : ρ.M = ∑ i ∈ s, p i • (ρs i).M)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1) (i : ι) (hi : i ∈ s) (hpi : 0 < p i) :
    ρs i = ρ := by
  have h_trace : ∀ j ∈ s, 0 < p j → (ρ.M.inner (ρs j).M = 1) := by
    have h_tr_pure : ∑ j ∈ s, p j • ρ.M.inner (ρs j).M = 1 := by
      have h_tr_pure : ρ.M.inner (∑ j ∈ s, p j • (ρs j).M) = ∑ j ∈ s, p j • ρ.M.inner (ρs j).M := by
        simp [ Finset.mul_sum _ _ _, HermitianMat.inner ];
      rw [ ← h_tr_pure, ← h_sum ];
      convert h_pure using 1;
      exact beq_eq_beq.mp rfl;
    have h_tr_le_one : ∀ j ∈ s, ρ.M.inner (ρs j).M ≤ 1 := by
      intro j hj
      have h_tr_le_one_j : ρ.M.inner (ρs j).M ≤ ρ.M.trace * (ρs j).M.trace := by
        apply_rules [ HermitianMat.inner_le_mul_trace ];
        · exact ρ.zero_le;
        · exact (ρs j).zero_le;
      simp_all only [smul_eq_mul, tr, mul_one, ge_iff_le]
      exact h_tr_le_one_j.trans ( h_sum ▸ ρ.tr.le );
    intro j hj hj_pos
    by_contra h_contra;
    have h_tr_lt_one : ∑ j ∈ s, p j • ρ.M.inner (ρs j).M < ∑ j ∈ s, p j := by
      apply Finset.sum_lt_sum;
      · exact fun i hi => mul_le_of_le_one_right ( hp_nonneg i hi ) ( h_tr_le_one i hi );
      · exact ⟨ j, hj, mul_lt_of_lt_one_right hj_pos ( lt_of_le_of_ne ( h_tr_le_one j hj ) h_contra ) ⟩;
    linarith;
  have h_eq : ρ.M = (ρs i).M := by
    have h_eq : (ρ.M - (ρs i).M).inner (ρ.M - (ρs i).M) = 0 := by
      have h_eq : (ρ.M - (ρs i).M).inner (ρ.M - (ρs i).M) = ρ.M.inner ρ.M - 2 * ρ.M.inner (ρs i).M + (ρs i).M.inner (ρs i).M := by
        simp [ HermitianMat.inner ];
        simp [ Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_mul_comm ( ρ.m ) ] ; ring;
      have h_eq : ρ.M.inner ρ.M = 1 ∧ (ρs i).M.inner (ρs i).M ≤ 1 := by
        have h_eq : ρ.M.inner ρ.M = 1 := by
          convert h_pure using 1;
          exact beq_eq_beq.mp rfl;
        have h_eq : ∀ (A : HermitianMat d ℂ), 0 ≤ A → A.trace = 1 → A.inner A ≤ 1 := by
          intros A hA_nonneg hA_trace
          have h_eq : A.inner A ≤ A.trace * A.trace := by
            apply HermitianMat.inner_le_mul_trace hA_nonneg hA_nonneg;
          aesop;
        exact ⟨ by assumption, h_eq _ ( ρs i |>.2 ) ( ρs i |>.3 ) ⟩;
      linarith [ h_trace i hi hpi, show 0 ≤ ( ρ.M - ( ρs i |> MState.M ) |> HermitianMat.inner ) ( ρ.M - ( ρs i |> MState.M ) ) from HermitianMat.inner_self_nonneg _ ];
    -- Since the inner product of a matrix with itself is zero if and only if the matrix is zero, we have ρ.M - (ρs i).M = 0.
    have h_zero : ρ.M - (ρs i).M = 0 := by
      apply inner_self_eq_zero.mp h_eq;
    exact eq_of_sub_eq_zero h_zero;
  exact MState.ext h_eq.symm

theorem purity_prod {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ρ₁ : MState d₁) (ρ₂ : MState d₂) : (ρ₁ ⊗ ρ₂).purity = ρ₁.purity * ρ₂.purity := by
  exact prod_inner_prod ρ₁ ρ₁ ρ₂ ρ₂

theorem Prob.mul_eq_one_iff (p q : Prob) : p * q = 1 ↔ p = 1 ∧ q = 1 := by
  obtain ⟨val, property⟩ := p
  obtain ⟨val_1, property_1⟩ := q
  apply Iff.intro
  · intro a
    apply And.intro
    · erw [ Subtype.mk_eq_mk ] at a ⊢
      nlinarith
    · erw [ Subtype.mk_eq_mk ] at a ⊢
      nlinarith
  · intro a
    simp_all only [mul_one]

theorem pure_eq_pure_iff {d : Type*} [Fintype d] [DecidableEq d] (ψ φ : Ket d) :
    pure ψ = pure φ ↔ ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • φ.vec := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · -- By definition of pure state, we have that ψ.vec * conj ψ.vec = φ.vec * conj φ.vec.
    have h_eq : ∀ i j, ψ.vec i * starRingEnd ℂ (ψ.vec j) = φ.vec i * starRingEnd ℂ (φ.vec j) := by
      intro i j;
      replace h := congr_arg ( fun ρ => ρ.M.toMat i j ) h ; aesop;
    -- Let $k$ be such that $\varphi_k \neq 0$.
    obtain ⟨k, hk⟩ : ∃ k, φ.vec k ≠ 0 := by
      exact φ.exists_ne_zero;
    -- Let $z = \frac{\psi_k}{\varphi_k}$. Then $|z| = 1$.
    obtain ⟨z, hz⟩ : ∃ z : ℂ, ψ.vec k = z * φ.vec k ∧ ‖z‖ = 1 := by
      specialize h_eq k k
      simp_all only [ne_eq]
      refine' ⟨ ψ.vec k / φ.vec k, _, _ ⟩ <;> simp_all [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      rw [ div_eq_iff ] <;> norm_cast at * <;> aesop;
    refine' ⟨ z, hz.2, funext fun i => _ ⟩;
    specialize h_eq i k
    simp_all
    -- Since $\overline{z} \cdot \overline{\varphi_k} \neq 0$, we can divide both sides of the equation by $\overline{z} \cdot \overline{\varphi_k}$.
    have h_div : ψ.vec i * starRingEnd ℂ z = φ.vec i := by
      exact mul_left_cancel₀ ( show starRingEnd ℂ ( φ.vec k ) ≠ 0 from by simpa [ Complex.ext_iff ] using hk ) ( by linear_combination' h_eq );
    rw [ ← h_div, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; aesop;
  · cases h
    rename_i h
    obtain ⟨left, right⟩ := h
    -- Since $|w| = 1$, we have $w \overline{w} = 1$, which simplifies the matrix to $\phi \overline{\phi}^T$.
    have h_simp : ∀ i j, ψ.vec i * star (ψ.vec j) = φ.vec i * star (φ.vec j) := by
      simp [ *, Complex.ext_iff ];
      intro i j; rw [ Complex.norm_def ] at left; simp_all [ Complex.normSq ];
      grind +ring;
    exact MState.ext_m ( by ext i j; simpa [ Matrix.vecMulVec ] using h_simp i j )

theorem pure_separable_imp_IsProd {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) (h : IsSeparable (pure ψ)) : ψ.IsProd := by
      obtain ⟨ ρLRs, ps, hps ⟩ := h;
      -- Since `pure ψ` is pure (`purity = 1`), by `MState.eq_of_sum_eq_pure`, for any `k` with `p_k > 0`, we have `pure ψ = ρL_k ⊗ ρR_k`.
      obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) ∧ (MState.pure ψ).M = (k.val.1).M ⊗ₖ (k.val.2).M := by
        have h_pure : (MState.pure ψ).purity = 1 := by
          exact ( pure_iff_purity_one _ ).mp ⟨ ψ, rfl ⟩;
        obtain ⟨k, hk⟩ : ∃ k : { x : MState d₁ × MState d₂ // x ∈ ρLRs }, 0 < (ps k : ℝ) := by
          exact ⟨ Classical.choose ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all ), Classical.choose_spec ( show ∃ k : ρLRs, 0 < ( ps k : ℝ ) from by exact not_forall_not.mp fun h => by have := ps.2; simp_all) ⟩;
        refine' ⟨ k, hk, _ ⟩;
        convert MState.eq_of_sum_eq_pure h_pure _ _ _ k _ _;
        rotate_left;
        exact Finset.univ;
        use fun x => ( ps x : ℝ );
        use fun x => MState.prod x.val.1 x.val.2;
        all_goals norm_cast;
        · exact fun i a => unitInterval.nonneg (ps i);
        · exact ps.2;
        · exact Finset.mem_univ k;
        · obtain ⟨val, property⟩ := k
          obtain ⟨fst, snd⟩ := val
          have fwd : 0 ≤ (ps ⟨(fst, snd), property⟩).1 := le_of_lt hk
          apply Iff.intro
          · intro a
            exact MState.ext_iff.mpr a.symm
          · intro a
            rw [← a]
            rfl
      -- Since `pure ψ` is pure (`purity = 1`), by `MState.pure_iff_purity_one`, `ρL_k = pure ξ` and `ρR_k = pure φ` for some `ξ, φ`.
      obtain ⟨ξ, hξ⟩ : ∃ ξ : MState d₁, k.val.1 = ξ ∧ ξ.purity = 1 := by
        have h_purity : (MState.pure ψ).purity = (k.val.1).purity * (k.val.2).purity := by
          convert MState.purity_prod _ _;
          exact MState.ext hk.2;
        have h_purity_one : (MState.pure ψ).purity = 1 := by
          exact ( pure_iff_purity_one _ ).mp ⟨ ψ, rfl ⟩;
        rw [ h_purity, Prob.mul_eq_one_iff ] at h_purity_one ; aesop
      obtain ⟨φ, hφ⟩ : ∃ φ : MState d₂, k.val.2 = φ ∧ φ.purity = 1 := by
        have h_purity_prod : (MState.pure ψ).purity = (k.val.1).purity * (k.val.2).purity := by
          convert MState.purity_prod _ _;
          exact MState.ext hk.2;
        have h_purity_one : (MState.pure ψ).purity = 1 := by
          exact pure_iff_purity_one _ |>.1 ⟨ ψ, rfl ⟩;
        aesop;
      -- Since `ξ` and `φ` are pure states, we have `ξ = pure ξ'` and `φ = pure φ'` for some `ξ', φ'`.
      obtain ⟨ξ', hξ'⟩ : ∃ ξ' : Ket d₁, ξ = MState.pure ξ' := by
        have := MState.pure_iff_purity_one ξ;
        exact this.mpr hξ.2
      obtain ⟨φ', hφ'⟩ : ∃ φ' : Ket d₂, φ = MState.pure φ' := by
        have := MState.pure_iff_purity_one φ; aesop;
      -- Since `pure ψ = pure ξ ⊗ pure φ`, we have `ψ = ξ ⊗ φ` up to a global phase `z`.
      have h_eq : (MState.pure ψ).M = (MState.pure (ξ' ⊗ φ')).M := by
        rw [ hk.2, hξ.1, hξ', hφ.1, hφ', MState.pure_prod_pure ];
        exact rfl;
      -- Since `pure ψ = pure (ξ' ⊗ φ')`, we have `ψ = ξ' ⊗ φ'` up to a global phase `z`.
      have h_eq_ket : ∃ z : ℂ, ‖z‖ = 1 ∧ ψ.vec = z • (ξ' ⊗ φ').vec := by
        have := MState.pure_eq_pure_iff ψ ( ξ' ⊗ φ' );
        exact this.mp ( MState.ext h_eq );
      obtain ⟨ z, hz₁, hz₂ ⟩ := h_eq_ket;
      use ⟨ fun i => z * ξ' i, ?_ ⟩, φ';
      ext ⟨ i, j ⟩ ; simp [ Ket.prod ];
      convert congr_fun hz₂ ( i, j ) using 1;
      exact mul_assoc _ _ _;
      simp [ hz₁]
      simpa [ Complex.normSq_eq_norm_sq ] using ξ'.normalized'

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  apply Iff.intro
  · exact pure_separable_imp_IsProd ψ
  · rintro ⟨ ξ, φ, rfl ⟩
    rw [pure_prod_pure ξ φ]
    exact IsSeparable_prod _ _;

/--
A mixed state is pure if and only if its rank is 1.
-/
theorem pure_iff_rank_eq_one {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    (∃ ψ, ρ = pure ψ) ↔ ρ.m.rank = 1 := by
  constructor <;> intro h;
  · obtain ⟨w, rfl⟩ := h
    -- The rank of the outer product of a vector with itself is 1.
    have h_rank : ∀ (v : d → ℂ), v ≠ 0 → Matrix.rank (Matrix.vecMulVec v (conj v)) = 1 := by
      intro v hv_ne_zero
      have h_outer_product : ∀ (u : d → ℂ), ∃ (c : ℂ), Matrix.mulVec (Matrix.vecMulVec v (conj v)) u = c • v := by
        intro u
        use ∑ i, (starRingEnd ℂ (v i)) * (u i);
        ext i; simp [ Matrix.vecMulVec, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      apply le_antisymm
      · have h_outer_product : LinearMap.range (Matrix.mulVecLin (Matrix.vecMulVec v (conj v))) ≤ Submodule.span ℂ {v} := by
          rintro x ⟨ u, rfl ⟩ ; obtain ⟨ c, hc ⟩ := h_outer_product u; aesop;
        exact le_trans ( Submodule.finrank_mono h_outer_product ) ( finrank_span_le_card _ ) |> le_trans <| by simp ;
      · contrapose! hv_ne_zero; simp_all [ Matrix.rank, Submodule.eq_bot_iff ] ;
        ext i; specialize hv_ne_zero ( Pi.single i 1 ) ; simp_all [ Matrix.vecMulVec ] ;
        simpa using congr_fun hv_ne_zero i;
    exact h_rank _ ( fun h => by simpa [ h ] using w.exists_ne_zero );
  · -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ.
    obtain ⟨ψ, hψ⟩ : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
      -- Since ρ is Hermitian and has rank 1, it must be of the form |ψ⟩⟨ψ| for some ket ψ. Use this fact.
      have h_pure : ∃ ψ : d → ℂ, ρ.m = Matrix.of (fun i j => ψ i * star (ψ j)) := by
        have h_rank : ρ.m.rank = 1 := h
        have h_herm : ρ.m.IsHermitian := by
          exact ρ.M.property
        have := h_herm.spectral_theorem;
        -- Since the rank of ρ.m is 1, the diagonal matrix in the spectral theorem must have exactly one non-zero entry.
        obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 ∧ ∀ j : d, j ≠ i → h_herm.eigenvalues j = 0 := by
          have h_diag : ∑ i : d, (if h_herm.eigenvalues i = 0 then 0 else 1) = 1 := by
            have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = 1 := by
              have h_diag : Matrix.rank (Matrix.diagonal (h_herm.eigenvalues)) = Matrix.rank (ρ.m) := by
                exact Eq.symm (Matrix.IsHermitian.rank_eq_rank_diagonal h_herm);
              exact h_diag.trans h_rank;
            rw [ Matrix.rank_diagonal ] at h_diag;
            simp [ Finset.sum_ite ];
            rw [ Fintype.card_subtype ] at h_diag ; exact h_diag;
          obtain ⟨i, hi⟩ : ∃ i : d, h_herm.eigenvalues i ≠ 0 := by
            exact not_forall.mp fun h => by simp [ h ] at h_diag;
          rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ] at h_diag;
          exact ⟨ i, hi, fun j hj => Classical.not_not.1 fun hj' => absurd h_diag ( by rw [ if_neg hi ] ; exact ne_of_gt ( lt_add_of_pos_right _ ( lt_of_lt_of_le ( by simp [ hj' ] ) ( Finset.single_le_sum ( fun x _ => by positivity ) ( Finset.mem_sdiff.2 ⟨ Finset.mem_univ j, by simp [ hj ] ⟩ ) ) ) ) ) ⟩;
        -- Since the diagonal matrix in the spectral theorem has exactly one non-zero entry, we can write ρ.m as |ψ⟩⟨ψ| for some ket ψ.
        use fun j => (h_herm.eigenvectorUnitary : Matrix d d ℂ) j i * Real.sqrt (h_herm.eigenvalues i);
        convert this using 1;
        ext j k; simp [ Matrix.mul_apply, Matrix.diagonal ]
        ring_nf
        rw [ Finset.sum_eq_single i ] <;> simp +contextual [ hi ];
        exact Or.inl <| Or.inl <| mod_cast Real.sq_sqrt <| by
          have := ρ.pos.eigenvalues_nonneg i;
          convert this using 1;
      exact h_pure;
    have h_norm : ∑ x, Complex.normSq (ψ x) = 1 := by
      have := ρ.tr';
      simp_all [ Complex.ext_iff, Matrix.trace ];
      simpa only [ Complex.normSq_apply, mul_comm ] using this.1;
    use ⟨ψ, by
      simpa [ Complex.normSq_eq_norm_sq ] using h_norm⟩
    generalize_proofs at *;
    refine' MState.ext_m _ ; aesop

/-
A ket on a product space is a product state if and only if its coefficient matrix has rank 1.
-/
theorem Ket.IsProd_iff_rank_eq_one {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (ψ : Ket (d₁ × d₂)) :
    ψ.IsProd ↔ (Matrix.of (fun i j => ψ (i, j))).rank = 1 := by
      rw [ Ket.IsProd_iff_mul_eq_mul ];
      constructor;
      · intro h;
        obtain ⟨ξ, ψ', hξψ'⟩ : ∃ ξ : d₁ → ℂ, ∃ ψ' : d₂ → ℂ, ∀ i j, ψ (i, j) = ξ i * ψ' j := by
          -- Let's choose any $j₀$ such that $\psi(i, j₀) \neq 0$ for some $i$.
          obtain ⟨j₀, hj₀⟩ : ∃ j₀ : d₂, ∃ i₀ : d₁, ψ (i₀, j₀) ≠ 0 := by
            have := ψ.exists_ne_zero;
            exact ⟨ this.choose.2, this.choose.1, this.choose_spec ⟩;
          choose i₀ hi₀ using hj₀;
          exact ⟨ fun i => ψ ( i, j₀ ) / ψ ( i₀, j₀ ), fun j => ψ ( i₀, j ), fun i j => by rw [ div_mul_eq_mul_div, eq_div_iff hi₀ ] ; linear_combination h i i₀ j j₀ ⟩;
        -- Since the matrix is a product of two vectors, its rank is 1.
        have h_rank : Matrix.rank (Matrix.of (fun i j => ξ i * ψ' j)) ≤ 1 := by
          -- The range of the matrix is spanned by the single vector ξ.
          have h_range : LinearMap.range (Matrix.mulVecLin (Matrix.of (fun i j => ξ i * ψ' j))) ≤ Submodule.span ℂ {ξ} := by
            rintro x ⟨ y, rfl ⟩;
            rw [ Submodule.mem_span_singleton ];
            exact ⟨ ∑ j, ψ' j * y j, by ext i; simp [ Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ⟩;
          exact le_trans ( Submodule.finrank_mono h_range ) ( finrank_span_le_card _ ) |> le_trans <| by norm_num;
        cases h_rank.eq_or_lt <;> simp_all [ Matrix.rank, Submodule.eq_bot_iff ];
        · convert ‹Module.finrank ℂ ( LinearMap.range ( Matrix.mulVecLin ( Matrix.of fun i j => ξ i * ψ' j ) ) ) = 1› using 3 ; aesop;
          · aesop;
          · ext; simp [hξψ'];
        · have := ψ.exists_ne_zero
          simp_all only [ne_eq, mul_eq_zero, not_or, Prod.exists, exists_and_left, exists_and_right]
          obtain ⟨left, right⟩ := this
          obtain ⟨w, h_2⟩ := left
          obtain ⟨w_1, h_3⟩ := right
          rename_i h_1
          specialize h_1 ( Pi.single w_1 1 )
          simp_all [ funext_iff]
      · rw [ Matrix.rank ];
        rw [ finrank_eq_one_iff' ]
        intro a i₁ i₂ j₁ j₂
        simp_all only [ne_eq, Subtype.forall, LinearMap.mem_range, Matrix.mulVecBilin_apply, forall_exists_index,
          Subtype.exists, Submodule.mk_eq_zero, SetLike.mk_smul_mk, Subtype.mk.injEq, forall_apply_eq_imp_iff,
          exists_and_left, exists_prop]
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        obtain ⟨left_1, right⟩ := right
        obtain ⟨w_1, h⟩ := left_1
        subst h
        obtain ⟨ c, hc ⟩ := right ( Pi.single j₁ 1 ) ;
        obtain ⟨ d, hd ⟩ := right ( Pi.single j₂ 1 ) ;
        simp_all [ funext_iff, Matrix.mulVec ] ;
        rw [ ← hc i₁, ← hd i₁, ← hc i₂, ← hd i₂ ] ; ring

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  have h1 := MState.pure_separable_iff_IsProd ψ;
  have h2 := Ket.IsProd_iff_rank_eq_one ψ;
  have h3 := MState.pure_iff_rank_eq_one ( ( MState.pure ψ ).traceLeft )
  simp_all
  have h4 : Matrix.rank ((MState.pure ψ).traceLeft.m) = Matrix.rank (Matrix.of (fun i j => ψ (i, j))) := by
    have h4 : (MState.pure ψ).traceLeft.m = Matrix.transpose (Matrix.conjTranspose (Matrix.of (fun i j => ψ (i, j))) * Matrix.of (fun i j => ψ (i, j))) := by
      ext i j
      simp [ MState.traceLeft, Matrix.traceLeft, Matrix.mul_apply ] ;
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _;
    rw [ h4, Matrix.rank_transpose, Matrix.rank_conjTranspose_mul_self ];
  grind

--TODO: Separable states are convex

section purification

/-- The purification of a mixed state. Always uses the full dimension of the Hilbert space (d) to
 purify, so e.g. an existing pure state with d=4 still becomes d=16 in the purification. The defining
 property is `MState.traceRight_of_purify`; see also `MState.purify'` for the bundled version. -/
def purify (ρ : MState d) : Ket (d × d) where
  vec := fun (i,j) ↦
    let ρ2 := ρ.Hermitian.eigenvectorUnitary i j
    ρ2 * (ρ.Hermitian.eigenvalues j).sqrt
  normalized' := by
    have h₁ := fun i ↦ ρ.pos.eigenvalues_nonneg i
    simp only [Complex.norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, h₁, Real.sq_sqrt,
      Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀ x, ∑ i : d, ‖ρ.Hermitian.eigenvectorUnitary i x‖ ^ 2 = 1 :=
      Matrix.unitaryGroup_row_norm ρ.Hermitian.eigenvectorUnitary
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, Matrix.traceRight]
  simp only [pure_apply, Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  -- By definition of eigenvectorUnitary and the properties of the unitary matrix and the eigenvalues, we can show that the matrix constructed from the purification is equal to ρ.
  have h_eigenvectorUnitary : ∀ i j, ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ((ρ.Hermitian.eigenvalues x).sqrt ^ 2) * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x) = ρ.M i j := by
    intro i j
    have h_eigenvectorUnitary : ρ.M = Matrix.of (fun i j => ∑ x, ρ.Hermitian.eigenvectorUnitary i x * ρ.Hermitian.eigenvalues x * starRingEnd ℂ (ρ.Hermitian.eigenvectorUnitary j x)) := by
      have := ρ.Hermitian.spectral_theorem;
      convert this using 1;
      ext i j; simp [ Matrix.mul_apply, Matrix.diagonal ] ;
    replace h_eigenvectorUnitary := congr_fun ( congr_fun h_eigenvectorUnitary i ) j
    simp_all only [toMat_apply, Matrix.IsHermitian.eigenvectorUnitary_apply, PiLp.ofLp_apply, Matrix.of_apply]
    congr! 2;
    norm_num [ Complex.ext_iff, sq ];
    exact Or.inl ( Real.mul_self_sqrt ( by exact ( ρ.pos.eigenvalues_nonneg _ ) ) );
  simp_all [ Complex.normSq, sq ];
  simpa only [ mul_assoc ] using h_eigenvectorUnitary i j

/-- `MState.purify` bundled with its defining property `MState.traceRight_of_purify`. -/
def purifyX (ρ : MState d) : { ψ : Ket (d × d) // (pure ψ).traceRight = ρ } :=
  ⟨ρ.purify, ρ.purify_spec⟩

end purification

@[simps]
def relabel (ρ : MState d₁) (e : d₂ ≃ d₁) : MState d₂ where
  M := ρ.M.reindex e.symm
  zero_le := (HermitianMat.zero_le_iff.trans (Matrix.posSemidef_submatrix_equiv e)).mpr <| ρ.pos
  tr := by simp [trace]

@[simp]
theorem relabel_m (ρ : MState d₁) (e : d₂ ≃ d₁) :
    (ρ.relabel e).m = ρ.m.submatrix e e := by
  rfl

@[simp]
theorem relabel_refl {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.relabel (Equiv.refl d) = ρ := by
  ext
  simp

@[simp]
theorem relabel_relabel {d d₂ d₃ : Type*}
    [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]
    (ρ : MState d) (e : d₂ ≃ d) (e₂ : d₃ ≃ d₂) : (ρ.relabel e).relabel e₂ = ρ.relabel (e₂.trans e) := by
  rfl

theorem eq_relabel_iff {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (σ : MState d₂) (h : d₁ ≃ d₂) :
    ρ = σ.relabel h ↔ ρ.relabel h.symm = σ := by
  simp only [MState.ext_iff, HermitianMat.ext_iff, toMat_M, relabel_m]
  exact ⟨(by simp[·]), (by simp[← ·])⟩

theorem relabel_comp {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (e : d₂ ≃ d₁) (f : d₃ ≃ d₂) :
    (ρ.relabel e).relabel f = ρ.relabel (f.trans e) := by
  ext
  simp

theorem relabel_cast {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁]
    [Fintype d₂] [DecidableEq d₂]
       (ρ : MState d₁) (e : d₂ = d₁) :
    ρ.relabel (Equiv.cast e) = cast (by have := e.symm; congr <;> (apply Subsingleton.helim; congr)) ρ := by
  ext i j
  simp only [relabel_M, Equiv.cast_symm, val_eq_coe, reindex_coe, toMat_M, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.cast_apply]
  rw [eq_comm] at e
  congr
  · apply Subsingleton.helim; congr
  · apply Subsingleton.helim; congr
  · symm; apply cast_heq
  · apply cast_heq
  · apply cast_heq

@[simp]
theorem spectrum_relabel {ρ : MState d} (e : d₂ ≃ d) :
    _root_.spectrum ℝ (ρ.relabel e).m = _root_.spectrum ℝ ρ.m := by
  ext1 v
  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
  rw [Algebra.algebraMap_eq_smul_one v]
  rw [MState.relabel_m, ← Matrix.submatrix_one_equiv e]
  rw [← Matrix.smul_apply, ← Matrix.submatrix_smul]
  rw [← Matrix.sub_apply, ← Matrix.submatrix_sub]
  rw [Matrix.isUnit_submatrix_equiv]
  rw [← Algebra.algebraMap_eq_smul_one v, ← spectrum.mem_iff]

--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

--PULLOUT
/--
If two functions from finite types have the same multiset of values, there exists a bijection between the domains that commutes with the functions.
-/
lemma exists_equiv_of_multiset_map_eq {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) (h : Multiset.map f Finset.univ.val = Multiset.map g Finset.univ.val) :
    ∃ e : α ≃ β, f = g ∘ e := by
  -- Since the multisets of values are equal, the cardinalities of the domains must be equal (as the multiset size is the cardinality of the domain). Thus there exists a bijection `σ : α ≃ β`.
  obtain ⟨σ, hσ⟩ : ∃ σ : α ≃ β, Multiset.map f Finset.univ.val = Multiset.map (g ∘ σ) Finset.univ.val := by
    have h_card : Fintype.card α = Fintype.card β := by
      simpa using congr_arg Multiset.card h;
    obtain σ := Fintype.equivOfCardEq h_card
    use σ
    have h_multiset_eq : Multiset.map g Finset.univ.val = Multiset.map (g ∘ σ) Finset.univ.val := by
      rw [ ← Multiset.map_univ_val_equiv σ ] ;
      rw [ Multiset.map_map ]
    exact h.trans h_multiset_eq;
  -- By `Multiset.map_univ_eq_iff`, there exists `e' : α ≃ α` such that `f = (g ∘ σ) ∘ e'`.
  obtain ⟨e', he'⟩ : ∃ e' : α ≃ α, f = (g ∘ σ) ∘ e' := by
    exact (Multiset.map_univ_eq_iff f (g ∘ ⇑σ)).mp hσ;
  exact ⟨ e'.trans σ, by simpa [ Function.comp ] using he' ⟩

/--
The multiset of values in the spectrum of a relabeled state is the same as the multiset of values in the spectrum of the original state.
-/
lemma multiset_spectrum_relabel_eq {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    (ρ : MState d₁) (e : d₂ ≃ d₁) :
    Multiset.map (ρ.relabel e).spectrum Finset.univ.val = Multiset.map ρ.spectrum Finset.univ.val := by
  have h_charpoly : Matrix.charpoly (ρ.relabel e).m = Matrix.charpoly ρ.m := by
    exact Matrix.charpoly_reindex e.symm ρ.m
  have h_eigenvalues : Multiset.map (ρ.relabel e).M.H.eigenvalues Finset.univ.val = Multiset.map ρ.M.H.eigenvalues Finset.univ.val := by
    have h_eigenvalues : Polynomial.roots (Matrix.charpoly (ρ.relabel e).m) = Polynomial.roots (Matrix.charpoly ρ.m) := by
      rw [h_charpoly];
    have := ρ.M.H.charpoly_roots_eq_eigenvalues ; have := ( ρ.relabel e ).M.H.charpoly_roots_eq_eigenvalues
    simp_all only [relabel_m, toMat_M, Complex.coe_algebraMap, Function.comp_apply, relabel_M, val_eq_coe,
      reindex_coe, Matrix.reindex_apply, Equiv.symm_symm]
    replace this := congr_arg ( fun m => m.map ( fun x => x.re ) ) this
    aesop;
  unfold MState.spectrum;
  ext
  rename_i a
  simp_all only [relabel_m, relabel_M, val_eq_coe, reindex_coe, toMat_M, Matrix.reindex_apply, Equiv.symm_symm]
  obtain ⟨val, property⟩ := a
  obtain ⟨left, right⟩ := property
  convert congr_arg ( fun m => Multiset.count val m ) h_eigenvalues using 1;
  · rw [ Multiset.count_map, Multiset.count_map ];
    simp [ Subtype.ext_iff ];
    congr! 2;
  · erw [ Multiset.count_map, Multiset.count_map ];
    congr! 2;
    exact beq_eq_beq.mp rfl

def spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  -- Apply the lemma exists_equiv_of_multiset_map_eq with the appropriate parameters.
  obtain ⟨w, h⟩ := exists_equiv_of_multiset_map_eq (fun p => ρ.spectrum p) (fun p => ρ.SWAP.spectrum p)
    (MState.multiset_spectrum_relabel_eq ρ ( Equiv.prodComm _ _ ).symm ▸ rfl)
  use w
  ext x
  simp_rw [h]
  rfl

@[simp]
theorem SWAP_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.SWAP = ρ :=
  rfl

@[simp]
theorem traceLeft_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceLeft = ρ.traceRight :=
  rfl

@[simp]
theorem traceRight_SWAP (ρ : MState (d₁ × d₂)) : ρ.SWAP.traceRight = ρ.traceLeft :=
  rfl

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc (ρ : MState ((d₁ × d₂) × d₃)) : MState (d₁ × d₂ × d₃) :=
  ρ.relabel (Equiv.prodAssoc d₁ d₂ d₃).symm

/-- The associator that re-clusters the parts of a quantum system. -/
def assoc' (ρ : MState (d₁ × d₂ × d₃)) : MState ((d₁ × d₂) × d₃) :=
  ρ.SWAP.assoc.SWAP.assoc.SWAP

@[simp]
theorem assoc_assoc' (ρ : MState (d₁ × d₂ × d₃)) : ρ.assoc'.assoc = ρ := by
  rfl

@[simp]
theorem assoc'_assoc (ρ : MState ((d₁ × d₂) × d₃)) : ρ.assoc.assoc' = ρ := by
  rfl

@[simp]
theorem traceLeft_right_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceRight = ρ.traceRight.traceLeft := by
  ext
  simpa [assoc, relabel, Matrix.traceLeft, traceLeft, Matrix.traceRight, traceRight]
    using Finset.sum_comm

@[simp]
theorem traceRight_left_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceLeft = ρ.traceLeft.traceRight := by
  rw [← ρ.assoc'.traceLeft_right_assoc, assoc_assoc']

@[simp]
theorem traceRight_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceRight = ρ.traceRight.traceRight := by
  simp [Matrix.traceRight, traceRight, Fintype.sum_prod_type]
  rfl

@[simp]
theorem traceLeft_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceLeft = ρ.traceLeft.traceLeft := by
  convert ρ.SWAP.assoc.SWAP.traceRight_assoc
  simp

@[simp]
theorem traceLeft_left_assoc (ρ : MState ((d₁ × d₂) × d₃)) :
    ρ.assoc.traceLeft.traceLeft = ρ.traceLeft := by
  ext
  simpa [assoc, relabel, traceLeft, Matrix.traceLeft, Matrix.of_apply, Fintype.sum_prod_type]
    using Finset.sum_comm

@[simp]
theorem traceRight_right_assoc' (ρ : MState (d₁ × d₂ × d₃)) :
    ρ.assoc'.traceRight.traceRight = ρ.traceRight := by
  simp [assoc']

--TODO: This naming is very inconsistent. Should be better about "prod" vs "kron"

theorem relabel_kron {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₁) :
    ((ρ.relabel e) ⊗ σ) = (ρ ⊗ σ).relabel (e.prodCongr (Equiv.refl d₂)) := by
  ext
  rfl --is this defeq abuse? I don't know

theorem kron_relabel {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (e : d₃ ≃ d₂) :
    (ρ ⊗ σ.relabel e) = (ρ ⊗ σ).relabel ((Equiv.refl d₁).prodCongr e) := by
  ext
  rfl

theorem prod_assoc {d₁ d₂ d₃ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      [Fintype d₃] [DecidableEq d₃] (ρ : MState d₁) (σ : MState d₂) (τ : MState d₃) :
    (ρ ⊗ (σ ⊗ τ)) = (ρ ⊗ σ ⊗ τ).relabel (Equiv.prodAssoc d₁ d₂ d₃).symm := by
  ext1; ext1; symm
  simpa [MState.prod, MState.relabel, -Matrix.kronecker_assoc']
    using Matrix.kronecker_assoc' ρ.m σ.m τ.m

section topology

/-- Mixed states inherit the subspace topology from matrices -/
instance : TopologicalSpace (MState d) :=
  TopologicalSpace.induced MState.M inferInstance

/-- The projection from mixed states to their Hermitian matrices is an embedding -/
theorem toMat_IsEmbedding : Topology.IsEmbedding (MState.M (d := d)) where
  eq_induced := rfl
  injective := @MState.ext _ _ _

instance : T3Space (MState d) :=
  Topology.IsEmbedding.t3Space toMat_IsEmbedding

instance : CompactSpace (MState d) := by
  constructor
  rw [(Topology.IsInducing.induced MState.M).isCompact_iff]
  suffices IsCompact (Set.Icc 0 1 ∩ { m | m.trace = 1} : Set (HermitianMat d ℂ)) by
    convert this
    ext1 m
    constructor
    · rintro ⟨ρ, _, rfl⟩
      simp [ρ.zero_le, ρ.le_one]
    · simpa using fun m_pos _ m_tr ↦ ⟨⟨m, m_pos, m_tr⟩, rfl⟩
  apply isCompact_Icc.inter_right
  refine isClosed_eq ?_ continuous_const
  rw [funext trace_eq_re_trace]
  fun_prop

noncomputable instance : MetricSpace (MState d) :=
  MetricSpace.induced MState.M MState.M_Injective inferInstance

theorem dist_eq (x y : MState d) : dist x y = dist x.M y.M := by
  rfl

instance : BoundedSpace (MState d) where
  bounded_univ :=
    CompactSpace.isCompact_univ.isBounded

@[fun_prop]
theorem Continuous_HermitianMat : Continuous (MState.M (d := d)) :=
  continuous_iff_le_induced.mpr fun _ => id

@[fun_prop]
theorem Continuous_Matrix : Continuous (MState.m (d := d)) := by
  unfold MState.m
  fun_prop

theorem image_M_isBounded (S : Set (MState d)) : Bornology.IsBounded (MState.M '' S) := by
  rw [← Bornology.isBounded_induced]
  exact Bornology.IsBounded.all S

end topology

section finprod

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀(i :ι), Fintype (dI i)] [∀(i :ι), DecidableEq (dI i)]

--PULLOUT
theorem Matrix.IsHermitian_piProd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (A : ∀ i, Matrix (d i) (d i) ℂ) (hA : ∀ i, (A i).IsHermitian) :
    (Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))).IsHermitian := by
  ext j k; simp
  exact Finset.prod_congr rfl fun i _ => by simpa using congr_fun ( congr_fun ( hA i ) ( j i ) ) ( k i ) ;

--PULLOUT
theorem Matrix.trace_piProd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (A : ∀ i, Matrix (d i) (d i) ℂ) :
    Matrix.trace (Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))) = ∏ i, Matrix.trace (A i) := by
  simp [Matrix.trace]
  exact Eq.symm (Fintype.prod_sum fun i j => A i j j)

--PULLOUT
set_option maxHeartbeats 400000 in
theorem Matrix.PosSemidef_piProd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]
    (A : ∀ i, Matrix (d i) (d i) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    (Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))).PosSemidef := by
  -- Let B i be the square root of A i. Let BigB be the pi-product of B i. Show that BigB.conjTranspose * BigB equals the pi-product of A i using Fintype.prod_sum. Then use Matrix.PosSemidef.conjTranspose_mul_self to conclude the proof.
  obtain ⟨B, hB⟩ : ∃ B : ∀ i, Matrix (d i) (d i) ℂ, ∀ i, (A i) = B i * star (B i) := by
    -- By definition of positive semi-definite matrices, each $A_i$ can be written as $B_i^* B_i$ for some matrix $B_i$.
    have h_decomp : ∀ i, ∃ B : Matrix (d i) (d i) ℂ, A i = B * star B := by
      intro i
      obtain ⟨B, hB⟩ : ∃ B : Matrix (d i) (d i) ℂ, A i = B.conjTranspose * B := by
        exact Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp (hA i)
      use B.conjTranspose;
      convert hB using 1;
      simp [ Matrix.star_eq_conjTranspose ];
    exact ⟨ fun i => Classical.choose ( h_decomp i ), fun i => Classical.choose_spec ( h_decomp i ) ⟩;
  have hBigB_conjTranspose_mul_BigB : Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i * star (B i)) (j i) (k i)) = Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i)) * star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i))) := by
    ext j k; simp [ Matrix.mul_apply]
    simp only [Finset.prod_sum, ← Finset.prod_mul_distrib];
    refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
    · simp [ funext_iff ];
    · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  simp_all [ Matrix.PosSemidef ];
  refine' ⟨ _, _ ⟩;
  · ext; simp [ Matrix.mul_apply, mul_comm ] ;
  · intro x
    set y := star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, B i (j i) (k i))) *ᵥ x
    have h_nonneg : 0 ≤ Star.star y ⬝ᵥ y := by
      exact dotProduct_star_self_nonneg y;
    convert h_nonneg using 1
    simp [ Matrix.dotProduct_mulVec]
    simp [ Matrix.dotProduct_mulVec, y ];
    simp [ Matrix.vecMul, dotProduct, mul_comm ];
    simp [ Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) where
  M := {
    val j k := ∏ (i : ι), (ρi i).m (j i) (k i)
    property := by
      have h_herm : ∀ i, (ρi i).m.IsHermitian := by
        exact fun i => Hermitian (ρi i);
      convert Matrix.IsHermitian_piProd _ h_herm
  }
  zero_le := by
    rw [HermitianMat.zero_le_iff]
    --Should be in Mathlib
    constructor
    · ext j k
      dsimp
      rw [map_prod]
      congr! with i
      exact Matrix.ext_iff.mpr ((ρi i).pos.isHermitian) (j i) (k i)
    · intro v
      have h_pos_def : Matrix.PosSemidef (Matrix.of (fun j k : (∀ i, dI i) => ∏ i, (ρi i).m (j i) (k i))) := by
        convert Matrix.PosSemidef_piProd _ _;
        · assumption;
        · exact fun i => pos (ρi i)
      exact h_pos_def.2 v
  tr := by
    have h_trace : ∀ i, Matrix.trace (ρi i).m = 1 := by
      exact fun i => tr' (ρi i);
    convert congr_arg Complex.re ( Matrix.trace_piProd fun i => ( ρi i ).m ) using 1;
    simp [h_trace]

/-- The n-copy "power" of a mixed state, with the standard basis indexed by pi types. -/
def npow (ρ : MState d) (n : ℕ) : MState (Fin n → d) :=
  piProd (fun _ ↦ ρ)

@[inherit_doc]
infixl:110 "⊗^" => MState.npow

end finprod

section posdef

theorem PosDef.kron {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {σ₁ : MState d₁} {σ₂ : MState d₂} (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) : (σ₁ ⊗ σ₂).m.PosDef :=
  hσ₁.kron hσ₂

theorem PosDef.relabel {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
    {ρ : MState d₁} (hρ : ρ.m.PosDef) (e : d₂ ≃ d₁) : (ρ.relabel e).m.PosDef :=
  Matrix.PosDef.reindex hρ e.symm

/-- If both states positive definite, so is their mixture. -/
theorem PosDef_mix {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (hσ₂ : σ₂.m.PosDef) (p : Prob) : (p [σ₁ ↔ σ₂]).m.PosDef :=
  Matrix.PosDef.Convex hσ₁ hσ₂ p.zero_le (1 - p).zero_le (by simp)

/-- If one state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₁ : σ₁.m.PosDef) (p : Prob) (hp : p ≠ 0) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  rw [← zero_lt_iff] at hp
  exact (hσ₁.smul hp).add_posSemidef (σ₂.pos.rsmul (1 - p).zero_le)

/-- If the second state is positive definite and the mixture is nondegenerate, their mixture is also positive definite. -/
theorem PosDef_mix_of_ne_one {d : Type*} [Fintype d] [DecidableEq d] {σ₁ σ₂ : MState d}
    (hσ₂ : σ₂.m.PosDef) (p : Prob) (hp : p ≠ 1) : (p [σ₁ ↔ σ₂]).m.PosDef := by
  have : 0 < 1 - p := by
    --TODO this is ridiculous, move to Prob
    contrapose! hp
    have : (1 : ℝ) - (p : ℝ) = (0 : ℝ) := by
      have := le_antisymm hp (1 - p).zero_le
      rw [Subtype.ext_iff] at this
      simpa using this
    ext
    change (p : ℝ) = 1
    linarith
  exact (hσ₂.smul this).posSemidef_add (σ₁.pos.rsmul p.zero_le)

theorem uniform_posDef {d : Type*} [Nonempty d] [Fintype d] [DecidableEq d] :
    (uniform (d := d)).m.PosDef := by
  simp [uniform, ofClassical, m, HermitianMat.diagonal]
  exact Fintype.card_pos

theorem posDef_of_unique {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) [Unique d] : ρ.m.PosDef := by
  rw [Subsingleton.allEq ρ uniform]
  exact uniform_posDef

end posdef

end MState
