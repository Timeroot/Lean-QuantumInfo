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
  tr : HermitianMat.trace M = 1

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
  rw [Subtype.mk_le_mk]
  simp only [HermitianMat.val_eq_coe, selfAdjoint.val_one]
  suffices h : ρ.m ≤ (1 : ℝ) • 1 by
    rw [one_smul] at h
    exact h
  apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ρ.pos 1).mp
  exact eigenvalue_le_one ρ

/-- The inner product of two MState's, as a real number between 0 and 1. -/
def inner (ρ : MState d) (σ : MState d) : Prob :=
  ⟨ρ.M.inner σ.M, ρ.M.inner_ge_zero ρ.zero_le σ.zero_le,
    (ρ.M.inner_le_mul_trace ρ.zero_le σ.zero_le).trans (by simp)⟩

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

theorem pure_inner (ψ φ : Ket d) : (pure ψ).inner (pure φ) = Braket.dot ψ φ := by sorry

@[simp]
theorem pure_of (ψ : Ket d) : (pure ψ).m i j = (ψ i) * conj (ψ j) := by
  rfl

/-- The purity of a state is Tr[ρ^2]. This is a `Prob`, because it is always between zero and one. -/
def purity (ρ : MState d) : Prob :=
  ⟨ρ.M.inner ρ.M, ⟨HermitianMat.inner_ge_zero ρ.zero_le ρ.zero_le,
    by simpa using  HermitianMat.inner_le_mul_trace ρ.zero_le ρ.zero_le⟩⟩

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
  sorry

end pure

section prod

def prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : MState (d₁ × d₂) where
  M := ρ₁.M ⊗ₖ ρ₂.M
  zero_le := HermitianMat.zero_le_iff.mpr (ρ₁.pos.PosSemidef_kronecker ρ₂.pos)
  tr := by simp

infixl:100 " ⊗ " => MState.prod

theorem inner_sep.apply (ξ1 ψ1 : MState d₁) (ξ2 ψ2 : MState d₂) :
((ξ1⊗ξ2).inner (ψ1⊗ψ2) : ℂ) = (ξ1.inner ψ1) * (ξ2.inner ψ2) := by
  sorry

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

/-- Spectrum of direct product. There is a permutation σ so that the spectrum of the direct product of
  ρ₁ and ρ₂, as permuted under σ, is the pairwise products of the spectra of ρ₁ and ρ₂. -/
theorem spectrum_prod (ρ₁ : MState d₁) (ρ₂ : MState d₂) : ∃(σ : d₁ × d₂ ≃ d₁ × d₂),
    ∀i, ∀j, MState.spectrum (ρ₁ ⊗ ρ₂) (σ (i, j)) = (ρ₁.spectrum i) * (ρ₂.spectrum j) := by
  sorry

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

/-- A pure state is separable iff the ket is a product state. -/
theorem pure_separable_iff_IsProd (ψ : Ket (d₁ × d₂)) :
    IsSeparable (pure ψ) ↔ ψ.IsProd := by
  sorry

/-- A pure state is separable iff the partial trace on the left is pure. -/
theorem pure_separable_iff_traceLeft_pure (ψ : Ket (d₁ × d₂)) : IsSeparable (pure ψ) ↔
    ∃ ψ₁, pure ψ₁ = (pure ψ).traceLeft := by
  sorry

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
    simp [mul_pow, Real.sq_sqrt, h₁, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_mul]
    have : ∀x, ∑ i : d, ‖ρ.Hermitian.eigenvectorBasis x i‖ ^ 2 = 1 :=
      sorry
    apply @RCLike.ofReal_injective ℂ
    simp_rw [this, one_mul, Matrix.IsHermitian.sum_eigenvalues_eq_trace]
    exact ρ.tr'

/-- The defining property of purification, that tracing out the purifying system gives the
 original mixed state. -/
@[simp]
theorem purify_spec (ρ : MState d) : (pure ρ.purify).traceRight = ρ := by
  ext i j
  simp_rw [purify, traceRight, Matrix.traceRight]
  simp only [pure_of, Ket.apply]
  simp only [map_mul]
  simp_rw [mul_assoc, mul_comm, ← mul_assoc (Complex.ofReal _), Complex.mul_conj]
  sorry

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

--TODO: Swap and assoc for kets.
--TODO: Connect these to unitaries (when they can be)

/-- The heterogeneous SWAP gate that exchanges the left and right halves of a quantum system.
  This can apply even when the two "halves" are of different types, as opposed to (say) the SWAP
  gate on quantum circuits that leaves the qubit dimensions unchanged. Notably, it is not unitary. -/
def SWAP (ρ : MState (d₁ × d₂)) : MState (d₂ × d₁) :=
  ρ.relabel (Equiv.prodComm d₁ d₂).symm

def spectrum_SWAP (ρ : MState (d₁ × d₂)) : ∃ e, ρ.SWAP.spectrum.relabel e = ρ.spectrum := by
  sorry

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

@[simp]
theorem traceNorm_eq_1 (ρ : MState d) : ρ.m.traceNorm = 1 :=
  have := calc (ρ.m.traceNorm : ℂ)
    _ = ρ.m.trace := ρ.pos.traceNorm_PSD_eq_trace
    _ = 1 := ρ.tr'
  Complex.ofReal_eq_one.mp this

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

def piProd (ρi : (i:ι) → MState (dI i)) : MState ((i:ι) → dI i) where
  M := {
    val j k := ∏ (i : ι), (ρi i).m (j i) (k i)
    property := sorry
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
      sorry
  tr := by
    sorry
    -- rw [HermitianMat.trace_eq_trace_rc]
    -- convert (Finset.prod_univ_sum (κ := dI) (fun _ ↦ Finset.univ) (fun i_1 x ↦ (ρi i_1).m x x)).symm
    -- symm
    -- apply Finset.prod_eq_one
    -- intro x hx
    -- exact (ρi x).tr

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
